{-# LANGUAGE MultiWayIf #-}

module Deftype
  ( moduleForDeftype,
    moduleForDeftypeInContext,
    bindingsForRegisteredType,
    memberArg,
  )
where

import Concretize
import Context
import Data.Maybe
import Env (addListOfBindings, new)
import Info
import Managed
import Obj
import StructUtils
import Template
import ToTemplate
import TypeError
import TypePredicates
import Types
import TypesToC
import Util
import Validate

{-# ANN module "HLint: ignore Reduce duplication" #-}

moduleForDeftypeInContext :: Context -> String -> [Ty] -> [XObj] -> Maybe Info -> Either TypeError (String, XObj, [XObj])
moduleForDeftypeInContext ctx name vars members info =
  let global = contextGlobalEnv ctx
      types = contextTypeEnv ctx
      path = contextPath ctx
      inner = either (const Nothing) Just (innermostModuleEnv ctx)
      previous =
        either
          (const Nothing)
          Just
          ( (lookupBinderInInternalEnv ctx (SymPath path name))
              <> (lookupBinderInGlobalEnv ctx (SymPath path name))
                >>= \b ->
                  replaceLeft
                    (NotFoundGlobal (SymPath path name))
                    ( case binderXObj b of
                        XObj (Mod ev et) _ _ -> Right (ev, et)
                        _ -> Left "Non module"
                    )
          )
   in moduleForDeftype inner types global path name vars members info previous

-- | This function creates a "Type Module" with the same name as the type being defined.
--   A type module provides a namespace for all the functions that area automatically
--   generated by a deftype.
moduleForDeftype :: Maybe Env -> TypeEnv -> Env -> [String] -> String -> [Ty] -> [XObj] -> Maybe Info -> Maybe (Env, TypeEnv) -> Either TypeError (String, XObj, [XObj])
moduleForDeftype innerEnv typeEnv env pathStrings typeName typeVariables rest i existingEnv =
  let moduleValueEnv = fromMaybe (new innerEnv (Just typeName)) (fmap fst existingEnv)
      moduleTypeEnv = fromMaybe (new (Just typeEnv) (Just typeName)) (fmap snd existingEnv)
      -- The variable 'insidePath' is the path used for all member functions inside the 'typeModule'.
      -- For example (module Vec2 [x Float]) creates bindings like Vec2.create, Vec2.x, etc.
      insidePath = pathStrings ++ [typeName]
   in do
        validateMemberCases typeEnv typeVariables rest
        let structTy = StructTy (ConcreteNameTy (SymPath pathStrings typeName)) typeVariables
        (okMembers, membersDeps) <- templatesForMembers typeEnv env insidePath structTy rest
        okInit <- binderForInit insidePath structTy rest
        (okStr, strDeps) <- binderForStrOrPrn typeEnv env insidePath structTy rest "str"
        (okPrn, _) <- binderForStrOrPrn typeEnv env insidePath structTy rest "prn"
        (okDelete, deleteDeps) <- binderForDelete typeEnv env insidePath structTy rest
        (okCopy, copyDeps) <- binderForCopy typeEnv env insidePath structTy rest
        let funcs = okInit : okStr : okPrn : okDelete : okCopy : okMembers
            moduleEnvWithBindings = addListOfBindings moduleValueEnv funcs
            typeModuleXObj = XObj (Mod moduleEnvWithBindings moduleTypeEnv) i (Just ModuleTy)
            deps = deleteDeps ++ membersDeps ++ copyDeps ++ strDeps
        pure (typeName, typeModuleXObj, deps)

-- | Will generate getters/setters/updaters when registering EXTERNAL types.
-- | i.e. (register-type VRUnicornData [hp Int, magic Float])
-- | TODO: Remove duplication shared by moduleForDeftype-function.
bindingsForRegisteredType :: TypeEnv -> Env -> [String] -> String -> [XObj] -> Maybe Info -> Maybe (Env, TypeEnv) -> Either TypeError (String, XObj, [XObj])
bindingsForRegisteredType typeEnv env pathStrings typeName rest i existingEnv =
  let moduleValueEnv = fromMaybe (new (Just env) (Just typeName)) (fmap fst existingEnv)
      moduleTypeEnv = fromMaybe (new (Just typeEnv) (Just typeName)) (fmap snd existingEnv)
      insidePath = pathStrings ++ [typeName]
   in do
        validateMemberCases typeEnv [] rest
        let structTy = StructTy (ConcreteNameTy (SymPath pathStrings typeName)) []
        (binders, deps) <- templatesForMembers typeEnv env insidePath structTy rest
        okInit <- binderForInit insidePath structTy rest
        (okStr, strDeps) <- binderForStrOrPrn typeEnv env insidePath structTy rest "str"
        (okPrn, _) <- binderForStrOrPrn typeEnv env insidePath structTy rest "prn"
        let moduleEnvWithBindings = addListOfBindings moduleValueEnv (okInit : okStr : okPrn : binders)
            typeModuleXObj = XObj (Mod moduleEnvWithBindings moduleTypeEnv) i (Just ModuleTy)
        pure (typeName, typeModuleXObj, deps ++ strDeps)

-- | Generate all the templates for ALL the member variables in a deftype declaration.
templatesForMembers :: TypeEnv -> Env -> [String] -> Ty -> [XObj] -> Either TypeError ([(String, Binder)], [XObj])
templatesForMembers typeEnv env insidePath structTy [XObj (Arr membersXobjs) _ _] =
  let bindersAndDeps = concatMap (templatesForSingleMember typeEnv env insidePath structTy) (pairwise membersXobjs)
   in Right (map fst bindersAndDeps, concatMap snd bindersAndDeps)
templatesForMembers _ _ _ _ _ = error "Shouldn't reach this case (invalid type definition)."

-- | Generate the templates for a single member in a deftype declaration.
templatesForSingleMember :: TypeEnv -> Env -> [String] -> Ty -> (XObj, XObj) -> [((String, Binder), [XObj])]
templatesForSingleMember typeEnv env insidePath p@(StructTy (ConcreteNameTy _) _) (nameXObj, typeXObj) =
  case t of
    -- Unit member types are special since we do not represent them in emitted c.
    -- Instead, members of type Unit are executed for their side effects and silently omitted
    -- from the produced C structs.
    UnitTy ->
      binders
        (FuncTy [RefTy p (VarTy "q")] UnitTy StaticLifetimeTy)
        (FuncTy [p, t] p StaticLifetimeTy)
        (FuncTy [RefTy p (VarTy "q"), t] UnitTy StaticLifetimeTy)
        (FuncTy [p, RefTy (FuncTy [] UnitTy (VarTy "fq")) (VarTy "q")] p StaticLifetimeTy)
    _ ->
      binders
        (FuncTy [RefTy p (VarTy "q")] (RefTy t (VarTy "q")) StaticLifetimeTy)
        (FuncTy [p, t] p StaticLifetimeTy)
        (FuncTy [RefTy p (VarTy "q"), t] UnitTy StaticLifetimeTy)
        (FuncTy [p, RefTy (FuncTy [t] t (VarTy "fq")) (VarTy "q")] p StaticLifetimeTy)
  where
    Just t = xobjToTy typeXObj
    memberName = getName nameXObj
    binders getterSig setterSig mutatorSig updaterSig =
      [ instanceBinderWithDeps (SymPath insidePath memberName) getterSig (templateGetter (mangle memberName) t) ("gets the `" ++ memberName ++ "` property of a `" ++ show p ++ "`."),
        if isTypeGeneric t
          then (templateGenericSetter insidePath p t memberName, [])
          else instanceBinderWithDeps (SymPath insidePath ("set-" ++ memberName)) setterSig (templateSetter typeEnv env (mangle memberName) t) ("sets the `" ++ memberName ++ "` property of a `" ++ show p ++ "`."),
        if isTypeGeneric t
          then (templateGenericMutatingSetter insidePath p t memberName, [])
          else instanceBinderWithDeps (SymPath insidePath ("set-" ++ memberName ++ "!")) mutatorSig (templateMutatingSetter typeEnv env (mangle memberName) t) ("sets the `" ++ memberName ++ "` property of a `" ++ show p ++ "` in place."),
        instanceBinderWithDeps
          (SymPath insidePath ("update-" ++ memberName))
          updaterSig
          (templateUpdater (mangle memberName) t)
          ("updates the `" ++ memberName ++ "` property of a `" ++ show p ++ "` using a function `f`.")
      ]
templatesForSingleMember _ _ _ _ _ = error "templatesforsinglemember"

-- | The template for getters of a deftype.
templateGetter :: String -> Ty -> Template
templateGetter _ UnitTy =
  Template
    (FuncTy [RefTy (VarTy "p") (VarTy "q")] UnitTy StaticLifetimeTy)
    (const (toTemplate "void $NAME($(Ref p) p)"))
    -- Execution of the action passed as an argument is handled in Emit.hs.
    (const $ toTemplate "$DECL { return; }\n")
    (const [])
templateGetter member memberTy =
  Template
    (FuncTy [RefTy (VarTy "p") (VarTy "q")] (VarTy "t") StaticLifetimeTy)
    (const (toTemplate "$t $NAME($(Ref p) p)"))
    ( \(FuncTy [_] retTy _) ->
        case retTy of
          (RefTy UnitTy _) -> toTemplate " $DECL { void* ptr = NULL; return ptr; }\n"
          _ ->
            let fixForVoidStarMembers =
                  if isFunctionType memberTy && not (isTypeGeneric memberTy)
                    then "(" ++ tyToCLambdaFix (RefTy memberTy (VarTy "q")) ++ ")"
                    else ""
             in toTemplate ("$DECL { return " ++ fixForVoidStarMembers ++ "(&(p->" ++ member ++ ")); }\n")
    )
    (const [])

-- | The template for setters of a concrete deftype.
templateSetter :: TypeEnv -> Env -> String -> Ty -> Template
templateSetter _ _ _ UnitTy =
  Template
    (FuncTy [VarTy "p", VarTy "t"] (VarTy "p") StaticLifetimeTy)
    (const (toTemplate "$p $NAME($p p)"))
    -- Execution of the action passed as an argument is handled in Emit.hs.
    (const (toTemplate "$DECL { return p; }\n"))
    (const [])
templateSetter typeEnv env memberName memberTy =
  let callToDelete = memberDeletion typeEnv env (memberName, memberTy)
   in Template
        (FuncTy [VarTy "p", VarTy "t"] (VarTy "p") StaticLifetimeTy)
        (const (toTemplate "$p $NAME($p p, $t newValue)"))
        ( const
            ( toTemplate
                ( unlines
                    [ "$DECL {",
                      callToDelete,
                      "    p." ++ memberName ++ " = newValue;",
                      "    return p;",
                      "}\n"
                    ]
                )
            )
        )
        ( \_ ->
            if
                | isManaged typeEnv env memberTy -> depsOfPolymorphicFunction typeEnv env [] "delete" (typesDeleterFunctionType memberTy)
                | isFunctionType memberTy -> [defineFunctionTypeAlias memberTy]
                | otherwise -> []
        )

-- | The template for setters of a generic deftype.
templateGenericSetter :: [String] -> Ty -> Ty -> String -> (String, Binder)
templateGenericSetter pathStrings originalStructTy@(StructTy (ConcreteNameTy _) _) membTy memberName =
  defineTypeParameterizedTemplate templateCreator path (FuncTy [originalStructTy, membTy] originalStructTy StaticLifetimeTy) docs
  where
    path = SymPath pathStrings ("set-" ++ memberName)
    t = FuncTy [VarTy "p", VarTy "t"] (VarTy "p") StaticLifetimeTy
    docs = "sets the `" ++ memberName ++ "` property of a `" ++ show originalStructTy ++ "`."
    templateCreator = TemplateCreator $
      \typeEnv env ->
        Template
          t
          ( \(FuncTy [_, memberTy] _ _) ->
              case memberTy of
                UnitTy -> toTemplate "$p $NAME($p p)"
                _ -> toTemplate "$p $NAME($p p, $t newValue)"
          )
          ( \(FuncTy [_, memberTy] _ _) ->
              let callToDelete = memberDeletion typeEnv env (memberName, memberTy)
               in case memberTy of
                    UnitTy -> toTemplate "$DECL { return p; }\n"
                    _ ->
                      toTemplate
                        ( unlines
                            [ "$DECL {",
                              callToDelete,
                              "    p." ++ memberName ++ " = newValue;",
                              "    return p;",
                              "}\n"
                            ]
                        )
          )
          ( \(FuncTy [_, memberTy] _ _) ->
              if isManaged typeEnv env memberTy
                then depsOfPolymorphicFunction typeEnv env [] "delete" (typesDeleterFunctionType memberTy)
                else []
          )
templateGenericSetter _ _ _ _ = error "templategenericsetter"

-- | The template for mutating setters of a deftype.
templateMutatingSetter :: TypeEnv -> Env -> String -> Ty -> Template
templateMutatingSetter _ _ _ UnitTy =
  Template
    (FuncTy [RefTy (VarTy "p") (VarTy "q"), VarTy "t"] UnitTy StaticLifetimeTy)
    (const (toTemplate "void $NAME($p* pRef)"))
    -- Execution of the action passed as an argument is handled in Emit.hs.
    (const (toTemplate "$DECL { return; }\n"))
    (const [])
templateMutatingSetter typeEnv env memberName memberTy =
  let callToDelete = memberRefDeletion typeEnv env (memberName, memberTy)
   in Template
        (FuncTy [RefTy (VarTy "p") (VarTy "q"), VarTy "t"] UnitTy StaticLifetimeTy)
        (const (toTemplate "void $NAME($p* pRef, $t newValue)"))
        ( const
            ( toTemplate
                ( unlines
                    [ "$DECL {",
                      callToDelete,
                      "    pRef->" ++ memberName ++ " = newValue;",
                      "}\n"
                    ]
                )
            )
        )
        (const [])

-- | The template for mutating setters of a generic deftype.
templateGenericMutatingSetter :: [String] -> Ty -> Ty -> String -> (String, Binder)
templateGenericMutatingSetter pathStrings originalStructTy@(StructTy (ConcreteNameTy _) _) membTy memberName =
  defineTypeParameterizedTemplate templateCreator path (FuncTy [RefTy originalStructTy (VarTy "q"), membTy] UnitTy StaticLifetimeTy) docs
  where
    path = SymPath pathStrings ("set-" ++ memberName ++ "!")
    t = FuncTy [RefTy (VarTy "p") (VarTy "q"), VarTy "t"] UnitTy StaticLifetimeTy
    docs = "sets the `" ++ memberName ++ "` property of a `" ++ show originalStructTy ++ "` in place."
    templateCreator = TemplateCreator $
      \typeEnv env ->
        Template
          t
          ( \(FuncTy [_, memberTy] _ _) ->
              case memberTy of
                UnitTy -> toTemplate "void $NAME($p* pRef)"
                _ -> toTemplate "void $NAME($p* pRef, $t newValue)"
          )
          ( \(FuncTy [_, memberTy] _ _) ->
              let callToDelete = memberRefDeletion typeEnv env (memberName, memberTy)
               in case memberTy of
                    UnitTy -> toTemplate "$DECL { return; }\n"
                    _ ->
                      toTemplate
                        ( unlines
                            [ "$DECL {",
                              callToDelete,
                              "    pRef->" ++ memberName ++ " = newValue;",
                              "}\n"
                            ]
                        )
          )
          ( \(FuncTy [_, memberTy] _ _) ->
              if isManaged typeEnv env memberTy
                then depsOfPolymorphicFunction typeEnv env [] "delete" (typesDeleterFunctionType memberTy)
                else []
          )
templateGenericMutatingSetter _ _ _ _ = error "templategenericmutatingsetter"

-- | The template for updater functions of a deftype.
-- | (allows changing a variable by passing an transformation function).
templateUpdater :: String -> Ty -> Template
templateUpdater _ UnitTy =
  Template
    (FuncTy [VarTy "p", RefTy (FuncTy [] UnitTy (VarTy "fq")) (VarTy "q")] (VarTy "p") StaticLifetimeTy)
    (const (toTemplate "$p $NAME($p p, Lambda *updater)")) -- "Lambda" used to be: $(Fn [t] t)
    -- Execution of the action passed as an argument is handled in Emit.hs.
    (const (toTemplate ("$DECL { " ++ templateCodeForCallingLambda "(*updater)" (FuncTy [] UnitTy (VarTy "fq")) [] ++ "; return p;}\n")))
    ( \(FuncTy [_, RefTy t@(FuncTy fArgTys fRetTy _) _] _ _) ->
        [defineFunctionTypeAlias t, defineFunctionTypeAlias (FuncTy (lambdaEnvTy : fArgTys) fRetTy StaticLifetimeTy)]
    )
templateUpdater member _ =
  Template
    (FuncTy [VarTy "p", RefTy (FuncTy [VarTy "t"] (VarTy "t") (VarTy "fq")) (VarTy "q")] (VarTy "p") StaticLifetimeTy)
    (const (toTemplate "$p $NAME($p p, Lambda *updater)")) -- "Lambda" used to be: $(Fn [t] t)
    ( const
        ( toTemplate
            ( unlines
                [ "$DECL {",
                  "    p." ++ member ++ " = " ++ templateCodeForCallingLambda "(*updater)" (FuncTy [VarTy "t"] (VarTy "t") (VarTy "fq")) ["p." ++ member] ++ ";",
                  "    return p;",
                  "}\n"
                ]
            )
        )
    )
    ( \(FuncTy [_, RefTy t@(FuncTy fArgTys fRetTy _) _] _ _) ->
        if isTypeGeneric fRetTy
          then []
          else [defineFunctionTypeAlias t, defineFunctionTypeAlias (FuncTy (lambdaEnvTy : fArgTys) fRetTy StaticLifetimeTy)]
    )

-- | Helper function to create the binder for the 'init' template.
binderForInit :: [String] -> Ty -> [XObj] -> Either TypeError (String, Binder)
binderForInit insidePath structTy@(StructTy (ConcreteNameTy _) _) [XObj (Arr membersXObjs) _ _] =
  if isTypeGeneric structTy
    then Right (genericInit StackAlloc insidePath structTy membersXObjs)
    else
      Right $
        instanceBinder
          (SymPath insidePath "init")
          (FuncTy (initArgListTypes membersXObjs) structTy StaticLifetimeTy)
          (concreteInit StackAlloc structTy membersXObjs)
          ("creates a `" ++ show structTy ++ "`.")
binderForInit _ _ _ = error "binderforinit"

-- | Generate a list of types from a deftype declaration.
initArgListTypes :: [XObj] -> [Ty]
initArgListTypes xobjs =
  map (fromJust . xobjToTy . snd) (pairwise xobjs)

-- | The template for the 'init' and 'new' functions for a concrete deftype.
concreteInit :: AllocationMode -> Ty -> [XObj] -> Template
concreteInit allocationMode originalStructTy@(StructTy (ConcreteNameTy _) _) membersXObjs =
  Template
    (FuncTy (map snd (memberXObjsToPairs membersXObjs)) (VarTy "p") StaticLifetimeTy)
    ( \(FuncTy _ concreteStructTy _) ->
        let mappings = unifySignatures originalStructTy concreteStructTy
            correctedMembers = replaceGenericTypeSymbolsOnMembers mappings membersXObjs
            memberPairs = memberXObjsToPairs correctedMembers
         in (toTemplate $ "$p $NAME(" ++ joinWithComma (map memberArg (unitless memberPairs)) ++ ")")
    )
    ( \(FuncTy _ concreteStructTy _) ->
        let mappings = unifySignatures originalStructTy concreteStructTy
            correctedMembers = replaceGenericTypeSymbolsOnMembers mappings membersXObjs
         in tokensForInit allocationMode (show originalStructTy) correctedMembers
    )
    (\FuncTy {} -> [])
  where
    unitless = remove (isUnit . snd)
concreteInit _ _ _ = error "concreteinit"

-- | The template for the 'init' and 'new' functions for a generic deftype.
genericInit :: AllocationMode -> [String] -> Ty -> [XObj] -> (String, Binder)
genericInit allocationMode pathStrings originalStructTy@(StructTy (ConcreteNameTy _) _) membersXObjs =
  defineTypeParameterizedTemplate templateCreator path t docs
  where
    path = SymPath pathStrings "init"
    t = FuncTy (map snd (memberXObjsToPairs membersXObjs)) originalStructTy StaticLifetimeTy
    docs = "creates a `" ++ show originalStructTy ++ "`."
    templateCreator = TemplateCreator $
      \typeEnv _ ->
        Template
          (FuncTy (map snd (memberXObjsToPairs membersXObjs)) (VarTy "p") StaticLifetimeTy)
          ( \(FuncTy _ concreteStructTy _) ->
              let mappings = unifySignatures originalStructTy concreteStructTy
                  correctedMembers = replaceGenericTypeSymbolsOnMembers mappings membersXObjs
                  memberPairs = memberXObjsToPairs correctedMembers
               in (toTemplate $ "$p $NAME(" ++ joinWithComma (map memberArg (remove (isUnit . snd) memberPairs)) ++ ")")
          )
          ( \(FuncTy _ concreteStructTy _) ->
              let mappings = unifySignatures originalStructTy concreteStructTy
                  correctedMembers = replaceGenericTypeSymbolsOnMembers mappings membersXObjs
               in tokensForInit allocationMode (show originalStructTy) correctedMembers
          )
          ( \(FuncTy _ concreteStructTy _) ->
              case concretizeType typeEnv concreteStructTy of
                Left err -> error (show err ++ ". This error should not crash the compiler - change return type to Either here.")
                Right ok -> ok
          )
genericInit _ _ _ _ = error "genericinit"

tokensForInit :: AllocationMode -> String -> [XObj] -> [Token]
tokensForInit allocationMode typeName membersXObjs =
  toTemplate $
    unlines
      [ "$DECL {",
        case allocationMode of
          StackAlloc -> case unitless of
            -- if this is truly a memberless struct, init it to 0;
            -- This can happen, e.g. in cases where *all* members of the struct are of type Unit.
            -- Since we do not generate members for Unit types.
            [] -> "    $p instance = {};"
            _ -> "    $p instance;"
          HeapAlloc -> "    $p instance = CARP_MALLOC(sizeof(" ++ typeName ++ "));",
        assignments membersXObjs,
        "    return instance;",
        "}"
      ]
  where
    assignments [] = "    instance.__dummy = 0;"
    assignments _ = go unitless
      where
        go [] = ""
        go xobjs = joinLines $ memberAssignment allocationMode . fst <$> xobjs
    unitless = remove (isUnit . snd) (memberXObjsToPairs membersXObjs)

-- | Creates the C code for an arg to the init function.
-- | i.e. "(deftype A [x Int])" will generate "int x" which
-- | will be used in the init function like this: "A_init(int x)"
memberArg :: (String, Ty) -> String
memberArg (memberName, memberTy) =
  tyToCLambdaFix (templatizeTy memberTy) ++ " " ++ memberName

-- | If the type is just a type variable; create a template type variable by appending $ in front of it's name
templatizeTy :: Ty -> Ty
templatizeTy (VarTy vt) = VarTy ("$" ++ vt)
templatizeTy (FuncTy argTys retTy ltTy) = FuncTy (map templatizeTy argTys) (templatizeTy retTy) (templatizeTy ltTy)
templatizeTy (StructTy name tys) = StructTy name (map templatizeTy tys)
templatizeTy (RefTy t lt) = RefTy (templatizeTy t) (templatizeTy lt)
templatizeTy (PointerTy t) = PointerTy (templatizeTy t)
templatizeTy t = t

-- | Helper function to create the binder for the 'str' template.
binderForStrOrPrn :: TypeEnv -> Env -> [String] -> Ty -> [XObj] -> String -> Either TypeError ((String, Binder), [XObj])
binderForStrOrPrn typeEnv env insidePath structTy@(StructTy (ConcreteNameTy _) _) [XObj (Arr membersXObjs) _ _] strOrPrn =
  if isTypeGeneric structTy
    then Right (genericStr insidePath structTy membersXObjs strOrPrn, [])
    else
      Right
        ( instanceBinderWithDeps
            (SymPath insidePath strOrPrn)
            (FuncTy [RefTy structTy (VarTy "q")] StringTy StaticLifetimeTy)
            (concreteStr typeEnv env structTy (memberXObjsToPairs membersXObjs) strOrPrn)
            ("converts a `" ++ show structTy ++ "` to a string.")
        )
binderForStrOrPrn _ _ _ _ _ _ = error "binderforstrorprn"

-- | The template for the 'str' function for a concrete deftype.
concreteStr :: TypeEnv -> Env -> Ty -> [(String, Ty)] -> String -> Template
concreteStr typeEnv env concreteStructTy@(StructTy (ConcreteNameTy name) _) memberPairs _ =
  Template
    (FuncTy [RefTy concreteStructTy (VarTy "q")] StringTy StaticLifetimeTy)
    (\(FuncTy [RefTy structTy _] StringTy _) -> toTemplate $ "String $NAME(" ++ tyToCLambdaFix structTy ++ " *p)")
    ( \(FuncTy [RefTy (StructTy _ _) _] StringTy _) ->
        tokensForStr typeEnv env (show name) memberPairs concreteStructTy
    )
    ( \(FuncTy [RefTy (StructTy _ _) (VarTy "q")] StringTy _) ->
        concatMap
          (depsOfPolymorphicFunction typeEnv env [] "prn" . typesStrFunctionType typeEnv env)
          (remove isFullyGenericType (map snd memberPairs))
    )
concreteStr _ _ _ _ _ = error "concretestr"

-- | The template for the 'str' function for a generic deftype.
genericStr :: [String] -> Ty -> [XObj] -> String -> (String, Binder)
genericStr pathStrings originalStructTy@(StructTy (ConcreteNameTy name) _) membersXObjs strOrPrn =
  defineTypeParameterizedTemplate templateCreator path t docs
  where
    path = SymPath pathStrings strOrPrn
    t = FuncTy [RefTy originalStructTy (VarTy "q")] StringTy StaticLifetimeTy
    docs = "converts a `" ++ show originalStructTy ++ "` to a string."
    templateCreator = TemplateCreator $
      \typeEnv env ->
        Template
          t
          ( \(FuncTy [RefTy concreteStructTy _] StringTy _) ->
              toTemplate $ "String $NAME(" ++ tyToCLambdaFix concreteStructTy ++ " *p)"
          )
          ( \(FuncTy [RefTy concreteStructTy@(StructTy _ _) _] StringTy _) ->
              let mappings = unifySignatures originalStructTy concreteStructTy
                  correctedMembers = replaceGenericTypeSymbolsOnMembers mappings membersXObjs
                  memberPairs = memberXObjsToPairs correctedMembers
               in tokensForStr typeEnv env (show name) memberPairs concreteStructTy
          )
          ( \ft@(FuncTy [RefTy concreteStructTy@(StructTy _ _) _] StringTy _) ->
              let mappings = unifySignatures originalStructTy concreteStructTy
                  correctedMembers = replaceGenericTypeSymbolsOnMembers mappings membersXObjs
                  memberPairs = memberXObjsToPairs correctedMembers
               in concatMap
                    (depsOfPolymorphicFunction typeEnv env [] "prn" . typesStrFunctionType typeEnv env)
                    (remove isFullyGenericType (map snd memberPairs))
                    ++ [defineFunctionTypeAlias ft | not (isTypeGeneric concreteStructTy)]
          )
genericStr _ _ _ _ = error "genericstr"

tokensForStr :: TypeEnv -> Env -> String -> [(String, Ty)] -> Ty -> [Token]
tokensForStr typeEnv env typeName memberPairs concreteStructTy =
  toTemplate $
    unlines
      [ "$DECL {",
        "  // convert members to String here:",
        "  String temp = NULL;",
        "  int tempsize = 0;",
        "  (void)tempsize; // that way we remove the occasional unused warning ",
        calculateStructStrSize typeEnv env memberPairs concreteStructTy,
        "  String buffer = CARP_MALLOC(size);",
        "  String bufferPtr = buffer;",
        "",
        "  sprintf(bufferPtr, \"(%s \", \"" ++ typeName ++ "\");",
        "  bufferPtr += strlen(\"" ++ typeName ++ "\") + 2;\n",
        joinLines (map (memberPrn typeEnv env) memberPairs),
        "  bufferPtr--;",
        "  sprintf(bufferPtr, \")\");",
        "  return buffer;",
        "}"
      ]

-- | Figure out how big the string needed for the string representation of the struct has to be.
calculateStructStrSize :: TypeEnv -> Env -> [(String, Ty)] -> Ty -> String
calculateStructStrSize typeEnv env members s@(StructTy (ConcreteNameTy _) _) =
  "  int size = snprintf(NULL, 0, \"(%s )\", \"" ++ show s ++ "\");\n"
    ++ unlines (map (memberPrnSize typeEnv env) members)
calculateStructStrSize _ _ _ _ = error "calculatestructstrsize"

-- | Generate C code for assigning to a member variable.
-- | Needs to know if the instance is a pointer or stack variable.
memberAssignment :: AllocationMode -> String -> String
memberAssignment allocationMode memberName = "    instance" ++ sep ++ memberName ++ " = " ++ memberName ++ ";"
  where
    sep = case allocationMode of
      StackAlloc -> "."
      HeapAlloc -> "->"

-- | Helper function to create the binder for the 'delete' template.
binderForDelete :: TypeEnv -> Env -> [String] -> Ty -> [XObj] -> Either TypeError ((String, Binder), [XObj])
binderForDelete typeEnv env insidePath structTy@(StructTy (ConcreteNameTy _) _) [XObj (Arr membersXObjs) _ _] =
  if isTypeGeneric structTy
    then Right (genericDelete insidePath structTy membersXObjs, [])
    else
      Right
        ( instanceBinderWithDeps
            (SymPath insidePath "delete")
            (FuncTy [structTy] UnitTy StaticLifetimeTy)
            (concreteDelete typeEnv env (memberXObjsToPairs membersXObjs))
            ("deletes a `" ++ show structTy ++ "`.")
        )
binderForDelete _ _ _ _ _ = error "binderfordelete"

-- | The template for the 'delete' function of a generic deftype.
genericDelete :: [String] -> Ty -> [XObj] -> (String, Binder)
genericDelete pathStrings originalStructTy@(StructTy (ConcreteNameTy _) _) membersXObjs =
  defineTypeParameterizedTemplate templateCreator path (FuncTy [originalStructTy] UnitTy StaticLifetimeTy) docs
  where
    path = SymPath pathStrings "delete"
    t = FuncTy [VarTy "p"] UnitTy StaticLifetimeTy
    docs = "deletes a `" ++ show originalStructTy ++ "`. Should usually not be called manually."
    templateCreator = TemplateCreator $
      \typeEnv env ->
        Template
          t
          (const (toTemplate "void $NAME($p p)"))
          ( \(FuncTy [concreteStructTy] UnitTy _) ->
              let mappings = unifySignatures originalStructTy concreteStructTy
                  correctedMembers = replaceGenericTypeSymbolsOnMembers mappings membersXObjs
                  memberPairs = memberXObjsToPairs correctedMembers
               in ( toTemplate $
                      unlines
                        [ "$DECL {",
                          joinLines (map (memberDeletion typeEnv env) memberPairs),
                          "}"
                        ]
                  )
          )
          ( \(FuncTy [concreteStructTy] UnitTy _) ->
              let mappings = unifySignatures originalStructTy concreteStructTy
                  correctedMembers = replaceGenericTypeSymbolsOnMembers mappings membersXObjs
                  memberPairs = memberXObjsToPairs correctedMembers
               in if isTypeGeneric concreteStructTy
                    then []
                    else
                      concatMap
                        (depsOfPolymorphicFunction typeEnv env [] "delete" . typesDeleterFunctionType)
                        (filter (isManaged typeEnv env) (map snd memberPairs))
          )
genericDelete _ _ _ = error "genericdelete"

-- | Helper function to create the binder for the 'copy' template.
binderForCopy :: TypeEnv -> Env -> [String] -> Ty -> [XObj] -> Either TypeError ((String, Binder), [XObj])
binderForCopy typeEnv env insidePath structTy@(StructTy (ConcreteNameTy _) _) [XObj (Arr membersXObjs) _ _] =
  if isTypeGeneric structTy
    then Right (genericCopy insidePath structTy membersXObjs, [])
    else
      Right
        ( instanceBinderWithDeps
            (SymPath insidePath "copy")
            (FuncTy [RefTy structTy (VarTy "q")] structTy StaticLifetimeTy)
            (concreteCopy typeEnv env (memberXObjsToPairs membersXObjs))
            ("copies a `" ++ show structTy ++ "`.")
        )
binderForCopy _ _ _ _ _ = error "binderforcopy"

-- | The template for the 'copy' function of a generic deftype.
genericCopy :: [String] -> Ty -> [XObj] -> (String, Binder)
genericCopy pathStrings originalStructTy@(StructTy (ConcreteNameTy _) _) membersXObjs =
  defineTypeParameterizedTemplate templateCreator path (FuncTy [RefTy originalStructTy (VarTy "q")] originalStructTy StaticLifetimeTy) docs
  where
    path = SymPath pathStrings "copy"
    t = FuncTy [RefTy (VarTy "p") (VarTy "q")] (VarTy "p") StaticLifetimeTy
    docs = "copies the `" ++ show originalStructTy ++ "`."
    templateCreator = TemplateCreator $
      \typeEnv env ->
        Template
          t
          (const (toTemplate "$p $NAME($p* pRef)"))
          ( \(FuncTy [RefTy concreteStructTy _] _ _) ->
              let mappings = unifySignatures originalStructTy concreteStructTy
                  correctedMembers = replaceGenericTypeSymbolsOnMembers mappings membersXObjs
                  memberPairs = memberXObjsToPairs correctedMembers
               in tokensForCopy typeEnv env memberPairs
          )
          ( \(FuncTy [RefTy concreteStructTy _] _ _) ->
              let mappings = unifySignatures originalStructTy concreteStructTy
                  correctedMembers = replaceGenericTypeSymbolsOnMembers mappings membersXObjs
                  memberPairs = memberXObjsToPairs correctedMembers
               in if isTypeGeneric concreteStructTy
                    then []
                    else
                      concatMap
                        (depsOfPolymorphicFunction typeEnv env [] "copy" . typesCopyFunctionType)
                        (filter (isManaged typeEnv env) (map snd memberPairs))
          )
genericCopy _ _ _ = error "genericcopy"
