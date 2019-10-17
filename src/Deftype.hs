{-# LANGUAGE MultiWayIf #-}

module Deftype (moduleForDeftype, bindingsForRegisteredType, memberArg) where

import qualified Data.Map as Map
import Data.Maybe
import Debug.Trace

import Obj
import Types
import Util
import Template
import ToTemplate
import Infer
import Concretize
import Polymorphism
import ArrayTemplates
import Lookup
import StructUtils
import TypeError
import Validate

{-# ANN module "HLint: ignore Reduce duplication" #-}
-- | This function creates a "Type Module" with the same name as the type being defined.
--   A type module provides a namespace for all the functions that area automatically
--   generated by a deftype.
moduleForDeftype :: TypeEnv -> Env -> [String] -> String -> [Ty] -> [XObj] -> Maybe Info -> Maybe Env -> Either TypeError (String, XObj, [XObj])
moduleForDeftype typeEnv env pathStrings typeName typeVariables rest i existingEnv =
  let typeModuleName = typeName
      typeModuleEnv = fromMaybe (Env (Map.fromList []) (Just env) (Just typeModuleName) [] ExternalEnv 0) existingEnv
      -- The variable 'insidePath' is the path used for all member functions inside the 'typeModule'.
      -- For example (module Vec2 [x Float]) creates bindings like Vec2.create, Vec2.x, etc.
      insidePath = pathStrings ++ [typeModuleName]
  in do validateMemberCases typeEnv typeVariables rest
        let structTy = StructTy typeName typeVariables
        (okMembers, membersDeps) <- templatesForMembers typeEnv env insidePath structTy rest
        okInit <- binderForInit insidePath structTy rest
        (okStr, strDeps) <- binderForStrOrPrn typeEnv env insidePath structTy rest "str"
        (okPrn, _) <- binderForStrOrPrn typeEnv env insidePath structTy rest "prn"
        (okDelete, deleteDeps) <- binderForDelete typeEnv env insidePath structTy rest
        (okCopy, copyDeps) <- binderForCopy typeEnv env insidePath structTy rest
        let funcs = okInit  : okStr : okPrn : okDelete : okCopy : okMembers
            moduleEnvWithBindings = addListOfBindings typeModuleEnv funcs
            typeModuleXObj = XObj (Mod moduleEnvWithBindings) i (Just ModuleTy)
            deps = deleteDeps ++ membersDeps ++ copyDeps ++ strDeps
        return (typeModuleName, typeModuleXObj, deps)

-- | Will generate getters/setters/updaters when registering EXTERNAL types.
-- | i.e. (register-type VRUnicornData [hp Int, magic Float])
-- | TODO: Remove duplication shared by moduleForDeftype-function.
bindingsForRegisteredType :: TypeEnv -> Env -> [String] -> String -> [XObj] -> Maybe Info -> Maybe Env -> Either TypeError (String, XObj, [XObj])
bindingsForRegisteredType typeEnv env pathStrings typeName rest i existingEnv =
  let typeModuleName = typeName
      typeModuleEnv = fromMaybe (Env (Map.fromList []) (Just env) (Just typeModuleName) [] ExternalEnv 0) existingEnv
      insidePath = pathStrings ++ [typeModuleName]
  in do validateMemberCases typeEnv [] rest
        let structTy = StructTy typeName []
        (binders, deps) <- templatesForMembers typeEnv env insidePath structTy rest
        okInit <- binderForInit insidePath structTy rest
        (okStr, strDeps) <- binderForStrOrPrn typeEnv env insidePath structTy rest "str"
        (okPrn, _) <- binderForStrOrPrn typeEnv env insidePath structTy rest "prn"
        let moduleEnvWithBindings = addListOfBindings typeModuleEnv (okInit : okStr : okPrn : binders)
            typeModuleXObj = XObj (Mod moduleEnvWithBindings) i (Just ModuleTy)
        return (typeModuleName, typeModuleXObj, deps ++ strDeps)



-- | Generate all the templates for ALL the member variables in a deftype declaration.
templatesForMembers :: TypeEnv -> Env -> [String] -> Ty -> [XObj] -> Either TypeError ([(String, Binder)], [XObj])
templatesForMembers typeEnv env insidePath structTy [XObj (Arr membersXobjs) _ _] =
  let bindersAndDeps = concatMap (templatesForSingleMember typeEnv env insidePath structTy) (pairwise membersXobjs)
  in  Right (map fst bindersAndDeps, concatMap snd bindersAndDeps)
templatesForMembers _ _ _ _ _ = error "Shouldn't reach this case (invalid type definition)."

-- | Generate the templates for a single member in a deftype declaration.
templatesForSingleMember :: TypeEnv -> Env -> [String] -> Ty -> (XObj, XObj) -> [((String, Binder), [XObj])]
templatesForSingleMember typeEnv env insidePath p@(StructTy typeName _) (nameXObj, typeXObj) =
  let Just t = xobjToTy typeXObj
      memberName = getName nameXObj
  in [instanceBinderWithDeps (SymPath insidePath memberName) (FuncTy [RefTy p (VarTy "q")] (RefTy t (VarTy "q"))) (templateGetter (mangle memberName) t) ("gets the `" ++ memberName ++ "` property of a `" ++ typeName ++ "`.")
     , if isTypeGeneric t
       then (templateGenericSetter insidePath p t memberName, [])
       else instanceBinderWithDeps (SymPath insidePath ("set-" ++ memberName)) (FuncTy [p, t] p) (templateSetter typeEnv env (mangle memberName) t) ("sets the `" ++ memberName ++ "` property of a `" ++ typeName ++ "`.")
     ,instanceBinderWithDeps (SymPath insidePath ("set-" ++ memberName ++ "!")) (FuncTy [RefTy p (VarTy "q"), t] UnitTy) (templateMutatingSetter typeEnv env (mangle memberName) t) ("sets the `" ++ memberName ++ "` property of a `" ++ typeName ++ "` in place.")
     ,instanceBinderWithDeps (SymPath insidePath ("update-" ++ memberName))
                                                            (FuncTy [p, RefTy (FuncTy [t] t) (VarTy "q")] p)
                                                            (templateUpdater (mangle memberName))
                                                            ("updates the `" ++ memberName ++ "` property of a `" ++ typeName ++ "` using a function `f`.")
                                                            ]

-- | The template for getters of a deftype.
templateGetter :: String -> Ty -> Template
templateGetter member memberTy =
  Template
    (FuncTy [RefTy (VarTy "p") (VarTy "q")] (VarTy "t"))
    (const (toTemplate "$t $NAME($(Ref p) p)"))
    (const $
     let fixForVoidStarMembers =
           if isFunctionType memberTy && not (isTypeGeneric memberTy)
           then "(" ++ tyToCLambdaFix (RefTy memberTy (VarTy "q")) ++ ")"
           else ""
     in  toTemplate ("$DECL { return " ++ fixForVoidStarMembers ++ "(&(p->" ++ member ++ ")); }\n"))
    (const [])

-- | The template for setters of a concrete deftype.
templateSetter :: TypeEnv -> Env -> String -> Ty -> Template
templateSetter typeEnv env memberName memberTy =
  let callToDelete = memberDeletion typeEnv env (memberName, memberTy)
  in
  Template
    (FuncTy [VarTy "p", VarTy "t"] (VarTy "p"))
    (const (toTemplate "$p $NAME($p p, $t newValue)"))
    (const (toTemplate (unlines ["$DECL {"
                                ,callToDelete
                                ,"    p." ++ memberName ++ " = newValue;"
                                ,"    return p;"
                                ,"}\n"])))
    (\_ -> if | isManaged typeEnv memberTy -> depsOfPolymorphicFunction typeEnv env [] "delete" (typesDeleterFunctionType memberTy)
              | isFunctionType memberTy -> [defineFunctionTypeAlias memberTy]
              | otherwise -> [])

-- | The template for setters of a generic deftype.
templateGenericSetter :: [String] -> Ty -> Ty -> String -> (String, Binder)
templateGenericSetter pathStrings originalStructTy@(StructTy typeName _) memberTy memberName =
  defineTypeParameterizedTemplate templateCreator path (FuncTy [originalStructTy, memberTy] originalStructTy) docs
  where path = SymPath pathStrings ("set-" ++ memberName)
        t = FuncTy [VarTy "p", VarTy "t"] (VarTy "p")
        docs = "sets the `" ++ memberName ++ "` property of a `" ++ typeName ++ "`."
        templateCreator = TemplateCreator $
          \typeEnv env ->
            Template
            t
            (const (toTemplate "$p $NAME($p p, $t newValue)"))
            (\(FuncTy [_, memberTy] _) ->
               let callToDelete = memberDeletion typeEnv env (memberName, memberTy)
               in  toTemplate (unlines ["$DECL {"
                                       ,callToDelete
                                       ,"    p." ++ memberName ++ " = newValue;"
                                       ,"    return p;"
                                       ,"}\n"]))
            (\(FuncTy [_, memberTy] _) ->
               if isManaged typeEnv memberTy
               then depsOfPolymorphicFunction typeEnv env [] "delete" (typesDeleterFunctionType memberTy)
               else [])

-- | The template for mutating setters of a deftype.
templateMutatingSetter :: TypeEnv -> Env -> String -> Ty -> Template
templateMutatingSetter typeEnv env memberName memberTy =
  let callToDelete = memberRefDeletion typeEnv env (memberName, memberTy)
  in Template
    (FuncTy [RefTy (VarTy "p") (VarTy "q"), VarTy "t"] UnitTy)
    (const (toTemplate "void $NAME($p* pRef, $t newValue)"))
    (const (toTemplate (unlines ["$DECL {"
                                ,callToDelete
                                ,"    pRef->" ++ memberName ++ " = newValue;"
                                ,"}\n"])))
    (const [])

-- | The template for updater functions of a deftype.
-- | (allows changing a variable by passing an transformation function).
templateUpdater :: String -> Template
templateUpdater member =
  Template
    (FuncTy [VarTy "p", RefTy (FuncTy [VarTy "t"] (VarTy "t")) (VarTy "q")] (VarTy "p"))
    (const (toTemplate "$p $NAME($p p, Lambda *updater)")) -- "Lambda" used to be: $(Fn [t] t)
    (const (toTemplate (unlines ["$DECL {"
                                ,"    p." ++ member ++ " = " ++ templateCodeForCallingLambda "(*updater)" (FuncTy [VarTy "t"] (VarTy "t")) ["p." ++ member] ++ ";"
                                ,"    return p;"
                                ,"}\n"])))
    (\(FuncTy [_, RefTy t@(FuncTy fArgTys fRetTy) _] _) ->
       if isTypeGeneric fRetTy
       then []
       else [defineFunctionTypeAlias t, defineFunctionTypeAlias (FuncTy (lambdaEnvTy : fArgTys) fRetTy)])

-- | Helper function to create the binder for the 'init' template.
binderForInit :: [String] -> Ty -> [XObj] -> Either TypeError (String, Binder)
binderForInit insidePath structTy@(StructTy typeName _) [XObj (Arr membersXObjs) _ _] =
  if isTypeGeneric structTy
  then Right (genericInit StackAlloc insidePath structTy membersXObjs)
  else Right $ instanceBinder (SymPath insidePath "init")
                (FuncTy (initArgListTypes membersXObjs) structTy)
                (concreteInit StackAlloc structTy membersXObjs)
                ("creates a `" ++ typeName ++ "`.")

-- | Generate a list of types from a deftype declaration.
initArgListTypes :: [XObj] -> [Ty]
initArgListTypes xobjs = map (\(_, x) -> fromJust (xobjToTy x)) (pairwise xobjs)

-- | The template for the 'init' and 'new' functions for a concrete deftype.
concreteInit :: AllocationMode -> Ty -> [XObj] -> Template
concreteInit allocationMode originalStructTy@(StructTy typeName typeVariables) membersXObjs =
  Template
    (FuncTy (map snd (memberXObjsToPairs membersXObjs)) (VarTy "p"))
    (\(FuncTy _ concreteStructTy) ->
     let mappings = unifySignatures originalStructTy concreteStructTy
         correctedMembers = replaceGenericTypeSymbolsOnMembers mappings membersXObjs
         memberPairs = memberXObjsToPairs correctedMembers
     in  (toTemplate $ "$p $NAME(" ++ joinWithComma (map memberArg memberPairs) ++ ")"))
    (const (tokensForInit allocationMode typeName membersXObjs))
    (\(FuncTy _ _) -> [])

-- | The template for the 'init' and 'new' functions for a generic deftype.
genericInit :: AllocationMode -> [String] -> Ty -> [XObj] -> (String, Binder)
genericInit allocationMode pathStrings originalStructTy@(StructTy typeName _) membersXObjs =
  defineTypeParameterizedTemplate templateCreator path t docs
  where path = SymPath pathStrings "init"
        t = FuncTy (map snd (memberXObjsToPairs membersXObjs)) originalStructTy
        docs = "creates a `" ++ typeName ++ "`."
        templateCreator = TemplateCreator $
          \typeEnv env ->
            Template
            (FuncTy (map snd (memberXObjsToPairs membersXObjs)) (VarTy "p"))
            (\(FuncTy _ concreteStructTy) ->
               let mappings = unifySignatures originalStructTy concreteStructTy
                   correctedMembers = replaceGenericTypeSymbolsOnMembers mappings membersXObjs
                   memberPairs = memberXObjsToPairs correctedMembers
               in  (toTemplate $ "$p $NAME(" ++ joinWithComma (map memberArg memberPairs) ++ ")"))
            (const (tokensForInit allocationMode typeName membersXObjs))
            (\(FuncTy _ concreteStructTy) ->
               case concretizeType typeEnv concreteStructTy of
                 Left err -> error (show err ++ ". This error should not crash the compiler - change return type to Either here.")
                 Right ok -> ok
            )

tokensForInit :: AllocationMode -> String -> [XObj] -> [Token]
tokensForInit allocationMode typeName membersXObjs =
  toTemplate $ unlines [ "$DECL {"
                       , case allocationMode of
                           StackAlloc -> "    $p instance;"
                           HeapAlloc ->  "    $p instance = CARP_MALLOC(sizeof(" ++ typeName ++ "));"
                       , joinWith "\n" (map (memberAssignment allocationMode) (memberXObjsToPairs membersXObjs))
                       , "    return instance;"
                       , "}"]

-- | Creates the C code for an arg to the init function.
-- | i.e. "(deftype A [x Int])" will generate "int x" which
-- | will be used in the init function like this: "A_init(int x)"
memberArg :: (String, Ty) -> String
memberArg (memberName, memberTy) =
  tyToCLambdaFix (templatizeTy memberTy) ++ " " ++ memberName

-- | If the type is just a type variable; create a template type variable by appending $ in front of it's name
templatizeTy :: Ty -> Ty
templatizeTy (VarTy vt) = VarTy ("$" ++ vt)
templatizeTy (FuncTy argTys retTy) = FuncTy (map templatizeTy argTys) (templatizeTy retTy)
templatizeTy (StructTy name tys) = StructTy name (map templatizeTy tys)
templatizeTy (RefTy t lt) = RefTy (templatizeTy t) (templatizeTy lt)
templatizeTy (PointerTy t) = PointerTy (templatizeTy t)
templatizeTy t = t

-- | Helper function to create the binder for the 'str' template.
binderForStrOrPrn :: TypeEnv -> Env -> [String] -> Ty -> [XObj] -> String -> Either TypeError ((String, Binder), [XObj])
binderForStrOrPrn typeEnv env insidePath structTy@(StructTy typeName _) [XObj (Arr membersXObjs) _ _] strOrPrn =
  if isTypeGeneric structTy
  then Right (genericStr insidePath structTy membersXObjs strOrPrn, [])
  else Right (instanceBinderWithDeps (SymPath insidePath strOrPrn)
              (FuncTy [RefTy structTy (VarTy "q")] StringTy)
              (concreteStr typeEnv env structTy (memberXObjsToPairs membersXObjs) strOrPrn)
              ("converts a `" ++ typeName ++ "` to a string."))

-- | The template for the 'str' function for a concrete deftype.
concreteStr :: TypeEnv -> Env -> Ty -> [(String, Ty)] -> String -> Template
concreteStr typeEnv env concreteStructTy@(StructTy typeName _) memberPairs strOrPrn =
  Template
    (FuncTy [RefTy concreteStructTy (VarTy "q")] StringTy)
    (\(FuncTy [RefTy structTy _] StringTy) -> toTemplate $ "String $NAME(" ++ tyToCLambdaFix structTy ++ " *p)")
    (\(FuncTy [RefTy structTy@(StructTy _ concreteMemberTys) _] StringTy) ->
        tokensForStr typeEnv env typeName memberPairs concreteStructTy)
    (\ft@(FuncTy [RefTy structTy@(StructTy _ concreteMemberTys) (VarTy "q")] StringTy) ->
       concatMap (depsOfPolymorphicFunction typeEnv env [] "prn" . typesStrFunctionType typeEnv)
                 (filter (\t -> (not . isExternalType typeEnv) t && (not . isFullyGenericType) t)
                  (map snd memberPairs)))

-- | The template for the 'str' function for a generic deftype.
genericStr :: [String] -> Ty -> [XObj] -> String -> (String, Binder)
genericStr pathStrings originalStructTy@(StructTy typeName varTys) membersXObjs strOrPrn =
  defineTypeParameterizedTemplate templateCreator path t docs
  where path = SymPath pathStrings strOrPrn
        t = FuncTy [RefTy originalStructTy (VarTy "q")] StringTy
        members = memberXObjsToPairs membersXObjs
        docs = "converts a `" ++ typeName ++ "` to a string."
        templateCreator = TemplateCreator $
          \typeEnv env ->
            Template
            t
            (\(FuncTy [RefTy concreteStructTy _] StringTy) ->
               toTemplate $ "String $NAME(" ++ tyToCLambdaFix concreteStructTy ++ " *p)")
            (\(FuncTy [RefTy concreteStructTy@(StructTy _ concreteMemberTys) _] StringTy) ->
               let mappings = unifySignatures originalStructTy concreteStructTy
                   correctedMembers = replaceGenericTypeSymbolsOnMembers mappings membersXObjs
                   memberPairs = memberXObjsToPairs correctedMembers
               in tokensForStr typeEnv env typeName memberPairs concreteStructTy)
            (\ft@(FuncTy [RefTy concreteStructTy@(StructTy _ concreteMemberTys) _] StringTy) ->
               let mappings = unifySignatures originalStructTy concreteStructTy
                   correctedMembers = replaceGenericTypeSymbolsOnMembers mappings membersXObjs
                   memberPairs = memberXObjsToPairs correctedMembers
               in  concatMap (depsOfPolymorphicFunction typeEnv env [] "prn" . typesStrFunctionType typeEnv)
                   (filter (\t -> (not . isExternalType typeEnv) t && (not . isFullyGenericType) t)
                    (map snd memberPairs))
                   ++
                   (if isTypeGeneric concreteStructTy then [] else [defineFunctionTypeAlias ft]))

tokensForStr :: TypeEnv -> Env -> String -> [(String, Ty)] -> Ty -> [Token]
tokensForStr typeEnv env typeName memberPairs concreteStructTy  =
  toTemplate $ unlines [ "$DECL {"
                        , "  // convert members to String here:"
                        , "  String temp = NULL;"
                        , "  int tempsize = 0;"
                        , "  (void)tempsize; // that way we remove the occasional unused warning "
                        , calculateStructStrSize typeEnv env memberPairs concreteStructTy
                        , "  String buffer = CARP_MALLOC(size);"
                        , "  String bufferPtr = buffer;"
                        , ""
                        , "  snprintf(bufferPtr, size, \"(%s \", \"" ++ typeName ++ "\");"
                        , "  bufferPtr += strlen(\"" ++ typeName ++ "\") + 2;\n"
                        , joinWith "\n" (map (memberPrn typeEnv env) memberPairs)
                        , "  bufferPtr--;"
                        , "  snprintf(bufferPtr, size, \")\");"
                        , "  return buffer;"
                        , "}"]

-- | Figure out how big the string needed for the string representation of the struct has to be.
calculateStructStrSize :: TypeEnv -> Env -> [(String, Ty)] -> Ty -> String
calculateStructStrSize typeEnv env members structTy@(StructTy name _) =
  "  int size = snprintf(NULL, 0, \"(%s )\", \"" ++ name ++ "\");\n" ++
  unlines (map (memberPrnSize typeEnv env) members)

-- | Generate C code for assigning to a member variable.
-- | Needs to know if the instance is a pointer or stack variable.
memberAssignment :: AllocationMode -> (String, Ty) -> String
memberAssignment allocationMode (memberName, _) = "    instance" ++ sep ++ memberName ++ " = " ++ memberName ++ ";"
  where sep = case allocationMode of
                StackAlloc -> "."
                HeapAlloc -> "->"

-- | Helper function to create the binder for the 'delete' template.
binderForDelete :: TypeEnv -> Env -> [String] -> Ty -> [XObj] -> Either TypeError ((String, Binder), [XObj])
binderForDelete typeEnv env insidePath structTy@(StructTy typeName _) [XObj (Arr membersXObjs) _ _] =
  if isTypeGeneric structTy
  then Right (genericDelete insidePath structTy membersXObjs, [])
  else Right (instanceBinderWithDeps (SymPath insidePath "delete")
             (FuncTy [structTy] UnitTy)
             (concreteDelete typeEnv env (memberXObjsToPairs membersXObjs))
             ("deletes a `" ++ typeName ++"`."))

-- | The template for the 'delete' function of a generic deftype.
genericDelete :: [String] -> Ty -> [XObj] -> (String, Binder)
genericDelete pathStrings originalStructTy@(StructTy typeName _) membersXObjs =
  defineTypeParameterizedTemplate templateCreator path (FuncTy [originalStructTy] UnitTy) docs
  where path = SymPath pathStrings "delete"
        t = FuncTy [VarTy "p"] UnitTy
        docs = "deletes a `" ++ typeName ++ "`. Should usually not be called manually."
        templateCreator = TemplateCreator $
          \typeEnv env ->
            Template
            t
            (const (toTemplate "void $NAME($p p)"))
            (\(FuncTy [concreteStructTy] UnitTy) ->
               let mappings = unifySignatures originalStructTy concreteStructTy
                   correctedMembers = replaceGenericTypeSymbolsOnMembers mappings membersXObjs
                   memberPairs = memberXObjsToPairs correctedMembers
               in  (toTemplate $ unlines [ "$DECL {"
                                         , joinWith "\n" (map (memberDeletion typeEnv env) memberPairs)
                                         , "}"]))
            (\(FuncTy [concreteStructTy] UnitTy) ->
               let mappings = unifySignatures originalStructTy concreteStructTy
                   correctedMembers = replaceGenericTypeSymbolsOnMembers mappings membersXObjs
                   memberPairs = memberXObjsToPairs correctedMembers
               in  if isTypeGeneric concreteStructTy
                   then []
                   else concatMap (depsOfPolymorphicFunction typeEnv env [] "delete" . typesDeleterFunctionType)
                                  (filter (isManaged typeEnv) (map snd memberPairs)))

-- | Helper function to create the binder for the 'copy' template.
binderForCopy :: TypeEnv -> Env -> [String] -> Ty -> [XObj] -> Either TypeError ((String, Binder), [XObj])
binderForCopy typeEnv env insidePath structTy@(StructTy typeName _) [XObj (Arr membersXObjs) _ _] =
  if isTypeGeneric structTy
  then Right (genericCopy insidePath structTy membersXObjs, [])
  else Right (instanceBinderWithDeps (SymPath insidePath "copy")
              (FuncTy [RefTy structTy (VarTy "q")] structTy)
              (concreteCopy typeEnv env (memberXObjsToPairs membersXObjs))
              ("copies a `" ++ typeName ++ "`."))

-- | The template for the 'copy' function of a generic deftype.
genericCopy :: [String] -> Ty -> [XObj] -> (String, Binder)
genericCopy pathStrings originalStructTy@(StructTy typeName _) membersXObjs =
  defineTypeParameterizedTemplate templateCreator path (FuncTy [RefTy originalStructTy (VarTy "q")] originalStructTy) docs
  where path = SymPath pathStrings "copy"
        t = FuncTy [RefTy (VarTy "p") (VarTy "q")] (VarTy "p")
        docs = "copies the `" ++ typeName ++ "`."
        templateCreator = TemplateCreator $
          \typeEnv env ->
            Template
            t
            (const (toTemplate "$p $NAME($p* pRef)"))
            (\(FuncTy [RefTy concreteStructTy _] _) ->
               let mappings = unifySignatures originalStructTy concreteStructTy
                   correctedMembers = replaceGenericTypeSymbolsOnMembers mappings membersXObjs
                   memberPairs = memberXObjsToPairs correctedMembers
               in tokensForCopy typeEnv env memberPairs)
            (\(FuncTy [RefTy concreteStructTy _] _) ->
               let mappings = unifySignatures originalStructTy concreteStructTy
                   correctedMembers = replaceGenericTypeSymbolsOnMembers mappings membersXObjs
                   memberPairs = memberXObjsToPairs correctedMembers
               in  if isTypeGeneric concreteStructTy
                   then []
                   else concatMap (depsOfPolymorphicFunction typeEnv env [] "copy" . typesCopyFunctionType)
                                  (filter (isManaged typeEnv) (map snd memberPairs)))
