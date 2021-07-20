{-# LANGUAGE LambdaCase #-}

module ArrayTemplates where

import Concretize
import Obj
import Polymorphism
import StructUtils
import Template
import ToTemplate
import Types
import TypesToC

arrayTyA :: Ty
arrayTyA = StructTy (ConcreteNameTy (SymPath [] "Array")) [(VarTy "a")]

arrayRef :: Ty
arrayRef = RefTy arrayTyA (VarTy "q")

-- | "Endofunctor Map"
templateEMap :: (String, Binder)
templateEMap =
  defineTypeParameterizedTemplate
    (TemplateCreator creatorFunc)
    (SymPath ["Array"] "endo-map")
    templateType
    documentation
  where
    templateType =
      FuncTy [RefTy endomorphism (VarTy "q"), arrayTyA] arrayTyA StaticLifetimeTy
    endomorphism = FuncTy [VarTy "a"] (VarTy "a") (VarTy "fq")
    documentation =
      "applies a function `f` to an array `a`. The type of the elements cannot change."
    creatorFunc :: TypeEnv -> Env -> Template
    creatorFunc _ _ =
      Template
        templateType
        (templateLiteral "Array $NAME(Lambda *f, Array a)")
        ( \(FuncTy [_, StructTy (ConcreteNameTy (SymPath [] "Array")) [memberTy]] _ _) ->
            handleUnits memberTy
        )
        ( \(FuncTy [RefTy t@(FuncTy fArgTys fRetTy _) _, _] _ _) ->
            [defineFunctionTypeAlias t, defineFunctionTypeAlias (FuncTy (lambdaEnvTy : fArgTys) fRetTy StaticLifetimeTy)]
        )
      where
        elt = "((($a*)a.data)[i])"
        handleUnits :: Ty -> [Token]
        handleUnits UnitTy = templateReturn "a"
        handleUnits _ =
          multilineTemplate
            [ "$DECL { ",
              "    for(int i = 0; i < a.len; ++i) {",
              "        (($a*)a.data)[i] = " ++ templateCodeForCallingLambda "(*f)" endomorphism [elt] ++ ";",
              "    }",
              "    return a;",
              "}"
            ]

templateShrinkCheck :: String -> String
templateShrinkCheck var =
  unlines
    [ "    if(" ++ var ++ ".len < (" ++ var ++ ".capacity / 4)) {",
      "        " ++ var ++ ".capacity = " ++ var ++ ".len * 2;",
      "        " ++ var ++ ".data = CARP_REALLOC(" ++ var ++ ".data, sizeof($a) * " ++ var ++ " .capacity);",
      "    }"
    ]

-- | Endofunctor filter, misnomer for consistency with flavors of map
templateEFilter :: (String, Binder)
templateEFilter = defineTypeParameterizedTemplate templateCreator path t docs
  where
    fTy = FuncTy [RefTy (VarTy "a") (VarTy "q")] BoolTy (VarTy "fq")
    path = SymPath ["Array"] "endo-filter"
    t = FuncTy [RefTy fTy (VarTy "w"), arrayTyA] arrayTyA StaticLifetimeTy
    docs = "filters array members using a function. This function takes ownership."
    elt = "&((($a*)a.data)[i])"
    declaration :: String -> (String -> String) -> [Token]
    declaration loopBody deleter =
      multilineTemplate
        [ "$DECL { ",
          "    int insertIndex = 0;",
          "    for(int i = 0; i < a.len; ++i) {",
          "        if(" ++ templateCodeForCallingLambda "(*predicate)" fTy [elt] ++ ") {",
          loopBody,
          "        } else {",
          "        " ++ deleter "i",
          "        }",
          "    }",
          "    a.len = insertIndex;",
          templateShrinkCheck "a",
          "    return a;",
          "}"
        ]
    templateCreator = TemplateCreator $
      \typeEnv env ->
        Template
          t
          (const (toTemplate "Array $NAME(Lambda *predicate, Array a)")) -- Lambda used to be $(Fn [(Ref a)] Bool)
          ( \(FuncTy [RefTy (FuncTy [RefTy insideTy _] BoolTy _) _, _] _ _) ->
              let deleteCall = insideArrayDeletion typeEnv env insideTy
               in ( case insideTy of
                      UnitTy -> declaration "           insertIndex++; /* ignore () member; just increment length. */" deleteCall
                      _ -> declaration "            ((($a*)a.data)[insertIndex++]) = (($a*)a.data)[i];" deleteCall
                  )
          )
          ( \(FuncTy [RefTy ft@(FuncTy fArgTys@[RefTy insideType _] BoolTy _) _, _] _ _) ->
              [defineFunctionTypeAlias ft, defineFunctionTypeAlias (FuncTy (lambdaEnvTy : fArgTys) BoolTy StaticLifetimeTy)]
                ++ depsForDeleteFunc typeEnv env insideType
          )

templatePushBack :: (String, Binder)
templatePushBack =
  defineTypeParameterizedTemplate creator path t docs
  where
    path = SymPath ["Array"] "push-back"
    valTy = VarTy "a"
    t = FuncTy [arrayTyA, valTy] arrayTyA StaticLifetimeTy
    docs = "adds an element `value` to the end of an array `a`."
    declaration :: String -> [Token]
    declaration setter =
      multilineTemplate
        [ "$DECL { ",
          "    a.len++;",
          "    if(a.len > a.capacity) {",
          "        a.capacity = a.len * 2;",
          "        a.data = CARP_REALLOC(a.data, sizeof($a) * a.capacity);",
          "    }",
          setter,
          "    return a;",
          "}"
        ]
    creator = TemplateCreator $
      \_ _ ->
        Template
          t
          ( \(FuncTy [_, valueTy] _ _) ->
              case valueTy of
                UnitTy -> toTemplate "Array $NAME(Array a)"
                _ -> toTemplate "Array $NAME(Array a, $a value)"
          )
          ( \(FuncTy [_, valueTy] _ _) ->
              case valueTy of
                UnitTy -> declaration "    /* ignore () member */"
                _ -> declaration "    (($a*)a.data)[a.len - 1] = value;"
          )
          (\(FuncTy [_, _] _ _) -> [])

templatePushBackBang :: (String, Binder)
templatePushBackBang =
  defineTypeParameterizedTemplate creator path t docs
  where
    path = SymPath ["Array"] "push-back!"
    valTy = VarTy "a"
    t = FuncTy [arrayRef, valTy] UnitTy StaticLifetimeTy
    docs = "adds an element `value` to the end of an array `a` in-place."
    declaration :: String -> [Token]
    declaration setter =
      multilineTemplate
        [ "$DECL { ",
          "    aRef->len++;",
          "    if(aRef->len > aRef->capacity) {",
          "        aRef->capacity = aRef->len * 2;",
          "        aRef->data = CARP_REALLOC(aRef->data, sizeof($a) * aRef->capacity);",
          "    }",
          setter,
          "}"
        ]
    creator = TemplateCreator $
      \_ _ ->
        Template
          t
          ( \(FuncTy [_, valueTy] _ _) ->
              case valueTy of
                UnitTy -> toTemplate "void $NAME(Array *aRef)"
                _ -> toTemplate "void $NAME(Array *aRef, $a value)"
          )
          ( \(FuncTy [_, valueTy] _ _) ->
              case valueTy of
                UnitTy -> declaration "    /* ignore () member */"
                _ -> declaration "    (($a*)aRef->data)[aRef->len - 1] = value;"
          )
          (\(FuncTy [_, _] _ _) -> [])

templatePopBack :: (String, Binder)
templatePopBack = defineTypeParameterizedTemplate templateCreator path t docs
  where
    path = SymPath ["Array"] "pop-back"
    t = FuncTy [arrayTyA] arrayTyA StaticLifetimeTy
    docs = "removes the last element of an array and returns the new array."
    templateCreator = TemplateCreator $
      \typeEnv env ->
        Template
          t
          (const (toTemplate "Array $NAME(Array a)"))
          ( \(FuncTy [StructTy _ [insideTy]] _ _) ->
              let deleteElement = insideArrayDeletion typeEnv env insideTy
               in toTemplate
                    ( unlines
                        [ "$DECL { ",
                          "  assert(a.len > 0);",
                          "  a.len--;",
                          "  " ++ deleteElement "a.len",
                          templateShrinkCheck "a",
                          "  return a;",
                          "}"
                        ]
                    )
          )
          ( \(FuncTy [arrayType@(StructTy _ [insideTy])] _ _) ->
              depsForDeleteFunc typeEnv env arrayType
                ++ depsForCopyFunc typeEnv env insideTy
          )

templatePopBackBang :: (String, Binder)
templatePopBackBang =
  defineTypeParameterizedTemplate creator path t docs
  where
    path = SymPath ["Array"] "pop-back!"
    t = FuncTy [arrayRef] (VarTy "a") StaticLifetimeTy
    docs = "removes an element `value` from the end of an array `a` in-place and returns it."
    creator =
      TemplateCreator $
        \_ _ ->
          Template
            t
            (templateLiteral "$a $NAME(Array *aRef)")
            ( \(FuncTy _ returnTy _) ->
                case returnTy of
                  UnitTy ->
                    multilineTemplate
                      [ "$DECL { ",
                        "  assert(aRef->len > 0);",
                        "  aRef->len--;",
                        "}"
                      ]
                  _ ->
                    multilineTemplate
                      [ "$DECL { ",
                        "  $a ret;",
                        "  assert(aRef->len > 0);",
                        "  ret = (($a*)aRef->data)[aRef->len - 1];",
                        "  aRef->len--;",
                        "  return ret;",
                        "}"
                      ]
            )
            (\(FuncTy [_] _ _) -> [])

templateNth :: (String, Binder)
templateNth =
  let t = VarTy "t"
   in defineTemplate
        (SymPath ["Array"] "unsafe-nth")
        (FuncTy [RefTy (StructTy (ConcreteNameTy (SymPath [] "Array")) [t]) (VarTy "q"), IntTy] (RefTy t (VarTy "q")) StaticLifetimeTy)
        "gets a reference to the `n`th element from an array `a`."
        (toTemplate "$t* $NAME (Array *aRef, int n)")
        ( toTemplate $
            unlines
              [ "$DECL {",
                "    Array a = *aRef;",
                "    assert(n >= 0);",
                "    assert(n < a.len);",
                "    return &((($t*)a.data)[n]);",
                "}"
              ]
        )
        ( \(FuncTy [RefTy _ _, _] _ _) ->
            []
        )

templateRaw :: (String, Binder)
templateRaw =
  defineTemplate
    (SymPath ["Array"] "raw")
    (FuncTy [StructTy (ConcreteNameTy (SymPath [] "Array")) [VarTy "t"]] (PointerTy (VarTy "t")) StaticLifetimeTy)
    "returns an array `a` as a raw pointer—useful for interacting with C."
    (toTemplate "$t* $NAME (Array a)")
    (toTemplate "$DECL { return a.data; }")
    (\(FuncTy [_] _ _) -> [])

templateUnsafeRaw :: (String, Binder)
templateUnsafeRaw =
  defineTemplate
    (SymPath ["Array"] "unsafe-raw")
    -- TODO: Fix me! Order of members of Ref is incorrect.
    (FuncTy [RefTy (VarTy "q") (StructTy (ConcreteNameTy (SymPath [] "Array")) [VarTy "t"])] (PointerTy (VarTy "t")) StaticLifetimeTy)
    "returns an array `a` as a raw pointer—useful for interacting with C."
    (toTemplate "$t* $NAME (Array* a)")
    (toTemplate "$DECL { return a->data; }")
    (\(FuncTy [RefTy _ _] _ _) -> [])

-- Several setter functions need to ensure the array's member type isn't Unit
-- Such setters only run a side effect, so we can even drop bounds checks.
unitSetterTemplate :: [Token]
unitSetterTemplate =
  multilineTemplate
    [ "$DECL {",
      "    /* () member, do nothing*/",
      "}"
    ]

templateAset :: (String, Binder)
templateAset = defineTypeParameterizedTemplate templateCreator path t docs
  where
    path = SymPath ["Array"] "aset"
    t = FuncTy [StructTy (ConcreteNameTy (SymPath [] "Array")) [VarTy "t"], IntTy, VarTy "t"] (StructTy (ConcreteNameTy (SymPath [] "Array")) [VarTy "t"]) StaticLifetimeTy
    docs = "sets an array element at the index `n` to a new value."
    templateCreator = TemplateCreator $
      \typeEnv env ->
        Template
          t
          ( \(FuncTy [_, _, insideTy] _ _) ->
              case insideTy of
                UnitTy -> toTemplate "Array $NAME (Array a, int n)"
                _ -> toTemplate "Array $NAME (Array a, int n, $t newValue)"
          )
          ( \(FuncTy [_, _, insideTy] _ _) ->
              case insideTy of
                -- Just return the same array for unit members.
                UnitTy -> toTemplate "$DECL { return a; }"
                _ ->
                  let deleter = insideArrayDeletion typeEnv env insideTy
                   in multilineTemplate
                        [ "$DECL {",
                          "    assert(n >= 0);",
                          "    assert(n < a.len);",
                          deleter "n",
                          "    (($t*)a.data)[n] = newValue;",
                          "    return a;",
                          "}"
                        ]
          )
          ( \(FuncTy [_, _, insideTy] _ _) ->
              depsForDeleteFunc typeEnv env insideTy
          )

templateAsetBang :: (String, Binder)
templateAsetBang = defineTypeParameterizedTemplate templateCreator path t docs
  where
    path = SymPath ["Array"] "aset!"
    t = FuncTy [RefTy (StructTy (ConcreteNameTy (SymPath [] "Array")) [VarTy "t"]) (VarTy "q"), IntTy, VarTy "t"] UnitTy StaticLifetimeTy
    docs = "sets an array element at the index `n` to a new value in place."
    templateCreator = TemplateCreator $
      \typeEnv env ->
        Template
          t
          ( \(FuncTy [_, _, valueType] _ _) ->
              case valueType of
                UnitTy -> toTemplate "void $NAME (Array *aRef, int n)"
                _ -> toTemplate "void $NAME (Array *aRef, int n, $t newValue)"
          )
          ( \(FuncTy [_, _, insideTy] _ _) ->
              case insideTy of
                UnitTy -> unitSetterTemplate
                _ ->
                  let deleter = insideArrayDeletion typeEnv env insideTy
                   in multilineTemplate
                        [ "$DECL {",
                          "    Array a = *aRef;",
                          "    assert(n >= 0);",
                          "    assert(n < a.len);",
                          deleter "n",
                          "    (($t*)a.data)[n] = newValue;",
                          "}"
                        ]
          )
          ( \(FuncTy [RefTy arrayType _, _, _] _ _) ->
              depsForDeleteFunc typeEnv env arrayType
          )

-- | This function can set uninitialized memory in an array (used together with 'allocate').
-- | It will NOT try to free the value that is already at location 'n'.
templateAsetUninitializedBang :: (String, Binder)
templateAsetUninitializedBang = defineTypeParameterizedTemplate templateCreator path t docs
  where
    path = SymPath ["Array"] "aset-uninitialized!"
    t = FuncTy [RefTy (StructTy (ConcreteNameTy (SymPath [] "Array")) [VarTy "t"]) (VarTy "q"), IntTy, VarTy "t"] UnitTy StaticLifetimeTy
    docs = "sets an uninitialized array member. The old member will not be deleted."
    templateCreator = TemplateCreator $
      \_ _ ->
        Template
          t
          ( \(FuncTy [_, _, valueType] _ _) ->
              case valueType of
                UnitTy -> toTemplate "void $NAME (Array *aRef, int n)"
                _ -> toTemplate "void $NAME (Array *aRef, int n, $t newValue)"
          )
          ( \(FuncTy [_, _, valueType] _ _) ->
              case valueType of
                UnitTy -> unitSetterTemplate
                _ ->
                  multilineTemplate
                    [ "$DECL {",
                      "    Array a = *aRef;",
                      "    assert(n >= 0);",
                      "    assert(n < a.len);",
                      "    (($t*)a.data)[n] = newValue;",
                      "}"
                    ]
          )
          (const [])

templateLength :: (String, Binder)
templateLength = defineTypeParameterizedTemplate templateCreator path t docs
  where
    path = SymPath ["Array"] "length"
    t = FuncTy [RefTy (StructTy (ConcreteNameTy (SymPath [] "Array")) [VarTy "t"]) (VarTy "q")] IntTy StaticLifetimeTy
    docs = "gets the length of the array."
    templateCreator = TemplateCreator $
      \typeEnv env ->
        Template
          t
          (const (toTemplate "int $NAME (Array *a)"))
          (const (toTemplate "$DECL { return (*a).len; }"))
          ( \(FuncTy [RefTy arrayType _] _ _) ->
              depsForDeleteFunc typeEnv env arrayType
          )

templateAllocate :: (String, Binder)
templateAllocate = defineTypeParameterizedTemplate templateCreator path t docs
  where
    path = SymPath ["Array"] "allocate"
    t = FuncTy [IntTy] (StructTy (ConcreteNameTy (SymPath [] "Array")) [VarTy "t"]) StaticLifetimeTy
    docs = "allocates an uninitialized array. You can initialize members using [`aset-uninitialized`](#aset-uninitialized)."
    templateCreator = TemplateCreator $
      \typeEnv env ->
        Template
          t
          (const (toTemplate "Array $NAME (int n)"))
          ( \(FuncTy [_] arrayType _) ->
              toTemplate $
                unlines
                  ( [ "$DECL {",
                      "    Array a;",
                      "    a.len = n;",
                      "    a.capacity = n;",
                      "    a.data = CARP_MALLOC(n*sizeof($t));"
                    ]
                      ++ initTy arrayType
                      ++ [ "    return a;",
                           "}"
                         ]
                  )
          )
          ( \(FuncTy [_] arrayType _) ->
              depsForDeleteFunc typeEnv env arrayType
          )

templateDeleteArray :: (String, Binder)
templateDeleteArray = defineTypeParameterizedTemplate templateCreator path t docs
  where
    path = SymPath ["Array"] "delete"
    t = FuncTy [arrayTyA] UnitTy StaticLifetimeTy
    docs = "deletes an array. This function should usually not be called manually."
    templateCreator = TemplateCreator $
      \typeEnv env ->
        Template
          t
          (const (toTemplate "void $NAME (Array a)"))
          ( \(FuncTy [arrayType] UnitTy _) ->
              [TokDecl, TokC "{\n"]
                ++ deleteTy typeEnv env arrayType
                ++ [TokC "}\n"]
          )
          ( \(FuncTy [StructTy (ConcreteNameTy (SymPath [] "Array")) [insideType]] UnitTy _) ->
              depsForDeleteFunc typeEnv env insideType
          )

deleteTy :: TypeEnv -> Env -> Ty -> [Token]
deleteTy typeEnv env (StructTy _ [innerType]) =
  [ TokC "    for(int i = 0; i < a.len; i++) {\n",
    TokC $ "    " ++ insideArrayDeletion typeEnv env innerType "i",
    TokC "    }\n",
    TokC "    CARP_FREE(a.data);\n"
  ]
deleteTy _ _ _ = []

initTy :: Ty -> [String]
initTy (StructTy (ConcreteNameTy (SymPath [] "Array")) [innerType@FuncTy {}]) =
  [ "    // initialize each Lambda struct ",
    "    for(int i = 0; i < a.len; i++) {",
    "    " ++ insideArrayInitLambda innerType "i",
    "    }"
  ]
initTy _ = []

insideArrayInitLambda :: Ty -> String -> String
insideArrayInitLambda (FuncTy _ UnitTy _) _ =
  "break;"
insideArrayInitLambda t indexer =
  "    Lambda lambda = "
    ++ initLambda
    ++ "\n"
    ++ "        (("
    ++ tyToCLambdaFix t
    ++ "*)a.data)["
    ++ indexer
    ++ "] = lambda;"

initLambda :: String
initLambda = "{ .callback = NULL, .env = NULL, .delete = NULL, .copy = NULL };"

insideArrayDeletion :: TypeEnv -> Env -> Ty -> String -> String
insideArrayDeletion typeEnv env t indexer =
  case findFunctionForMember typeEnv env "delete" (typesDeleterFunctionType t) ("Inside array.", t) of
    FunctionFound functionFullName ->
      "    " ++ functionFullName ++ "(((" ++ tyToCLambdaFix t ++ "*)a.data)[" ++ indexer ++ "]);\n"
    FunctionNotFound msg -> error msg
    FunctionIgnored -> "    /* Ignore non-managed type inside Array: '" ++ show t ++ "' */\n"

templateCopyArray :: (String, Binder)
templateCopyArray = defineTypeParameterizedTemplate templateCreator path t docs
  where
    path = SymPath ["Array"] "copy"
    t = FuncTy [arrayRef] arrayTyA StaticLifetimeTy
    docs = "copies an array."
    templateCreator = TemplateCreator $
      \typeEnv env ->
        Template
          t
          (const (toTemplate "Array $NAME (Array* a)"))
          ( \(FuncTy [RefTy arrayType _] _ _) ->
              [TokDecl, TokC "{\n"]
                ++ [TokC "    Array copy;\n"]
                ++ [TokC "    copy.len = a->len;\n"]
                ++ [TokC "    copy.capacity = a->capacity;\n"]
                ++ [TokC "    copy.data = CARP_MALLOC(sizeof(", TokTy (VarTy "a") Normal, TokC ") * a->capacity);\n"]
                ++ copyTy typeEnv env arrayType
                ++ [TokC "    return copy;\n"]
                ++ [TokC "}\n"]
          )
          ( \case
              (FuncTy [RefTy arrayType@(StructTy (ConcreteNameTy (SymPath [] "Array")) [insideType]) _] _ _) ->
                depsForCopyFunc typeEnv env insideType
                  ++ depsForDeleteFunc typeEnv env arrayType
              err ->
                error ("CAN'T MATCH: " ++ show err)
          )

copyTy :: TypeEnv -> Env -> Ty -> [Token]
copyTy typeEnv env (StructTy (ConcreteNameTy (SymPath [] "Array")) [innerType]) =
  if managed
    then
      [ TokC "    for(int i = 0; i < a->len; i++) {\n",
        TokC $ "    " ++ insideArrayCopying typeEnv env innerType,
        TokC "    }\n"
      ]
    else [TokC "    memcpy(copy.data, a->data, sizeof(", TokTy (VarTy "a") Normal, TokC ") * a->len);\n"]
  where
    managed =
      case findFunctionForMember
        typeEnv
        env
        "delete"
        (typesDeleterFunctionType innerType)
        ("Inside array.", innerType) of
        FunctionFound _ -> True
        FunctionNotFound _ -> False
        FunctionIgnored -> False
copyTy _ _ _ = []

-- | The "memberCopy" and "memberDeletion" functions in Deftype are very similar!
insideArrayCopying :: TypeEnv -> Env -> Ty -> String
insideArrayCopying typeEnv env t =
  case findFunctionForMemberIncludePrimitives typeEnv env "copy" (typesCopyFunctionType t) ("Inside array.", t) of
    FunctionFound functionFullName ->
      "    ((" ++ tyToC t ++ "*)(copy.data))[i] = " ++ functionFullName ++ "(&(((" ++ tyToC t ++ "*)a->data)[i]));\n"
    FunctionNotFound msg -> error msg
    FunctionIgnored ->
      "    /* Ignore type inside Array when copying: '" ++ show t ++ "' (no copy function known)*/\n"

templateStrArray :: (String, Binder)
templateStrArray = defineTypeParameterizedTemplate templateCreator path t docs
  where
    templateCreator = TemplateCreator $
      \typeEnv env ->
        Template
          t
          (const (toTemplate "String $NAME (Array* a)"))
          ( \(FuncTy [RefTy arrayType _] StringTy _) ->
              [TokDecl, TokC " {\n"]
                ++ strTy typeEnv env arrayType
                ++ [TokC "}\n"]
          )
          ( \(FuncTy [RefTy (StructTy (ConcreteNameTy (SymPath [] "Array")) [insideType]) _] StringTy _) ->
              depsForPrnFunc typeEnv env insideType
          )
    path = SymPath ["Array"] "str"
    t = FuncTy [arrayRef] StringTy StaticLifetimeTy
    docs = "converts an array to a string."

-- | TODO: move this into the templateStrArray function?
strTy :: TypeEnv -> Env -> Ty -> [Token]
strTy typeEnv env (StructTy _ [innerType]) =
  [ TokC "",
    TokC "  String temp = NULL;\n",
    TokC $ calculateStrSize typeEnv env innerType,
    TokC "  String buffer = CARP_MALLOC(size);\n",
    TokC "  String bufferPtr = buffer;\n",
    TokC "\n",
    TokC "  sprintf(buffer, \"[\");\n",
    TokC "  bufferPtr += 1;\n",
    TokC "\n",
    TokC "  for(int i = 0; i < a->len; i++) {\n",
    TokC $ "  " ++ insideArrayStr typeEnv env innerType,
    TokC "  }\n",
    TokC "\n",
    TokC "  if(a->len > 0) { bufferPtr -= 1; }\n",
    TokC "  sprintf(bufferPtr, \"]\");\n",
    TokC "  return buffer;\n"
  ]
strTy _ _ _ = []

strTakesRefOrNot :: TypeEnv -> Env -> Ty -> String
strTakesRefOrNot typeEnv env t =
  fst $ memberStrCallingConvention "str" typeEnv env t

calculateStrSize :: TypeEnv -> Env -> Ty -> String
calculateStrSize typeEnv env t =
  case t of
    -- If the member type is Unit, don't access the element.
    UnitTy -> makeTemplate (++ "();")
    _ -> makeTemplate (++ "(" ++ strTakesRefOrNot typeEnv env t ++ "((" ++ tyToC t ++ "*)a->data)[i]);")
  where
    makeTemplate :: (String -> String) -> String
    makeTemplate strcall =
      unlines
        [ "  int size = 3; // opening and closing brackets and terminator",
          "  for(int i = 0; i < a->len; i++) {",
          arrayMemberSizeCalc strcall ++ "  }",
          ""
        ]
    -- Get the size of the member type's string representation
    arrayMemberSizeCalc :: (String -> String) -> String
    arrayMemberSizeCalc strcall =
      case findFunctionForMemberIncludePrimitives typeEnv env "prn" (typesStrFunctionType typeEnv env t) ("Inside array.", t) of
        FunctionFound functionFullName ->
          unlines
            [ "    temp = " ++ strcall functionFullName,
              "    size += snprintf(NULL, 0, \"%s \", temp);",
              "    if(temp) {",
              "      CARP_FREE(temp);",
              "      temp = NULL;",
              "    }"
            ]
        FunctionNotFound msg -> error msg
        FunctionIgnored -> "    /* Ignore type inside Array: '" ++ show t ++ "' ??? */\n"

insideArrayStr :: TypeEnv -> Env -> Ty -> String
insideArrayStr typeEnv env t =
  case t of
    UnitTy -> makeTemplate (++ "();")
    _ -> makeTemplate (++ "(" ++ strTakesRefOrNot typeEnv env t ++ "((" ++ tyToC t ++ "*)a->data)[i]);")
  where
    makeTemplate :: (String -> String) -> String
    makeTemplate strcall =
      case findFunctionForMemberIncludePrimitives typeEnv env "prn" (typesStrFunctionType typeEnv env t) ("Inside array.", t) of
        FunctionFound functionFullName ->
          unlines
            [ "  temp = " ++ strcall functionFullName,
              "    sprintf(bufferPtr, \"%s \", temp);",
              "    bufferPtr += strlen(temp) + 1;",
              "    if(temp) {",
              "      CARP_FREE(temp);",
              "      temp = NULL;",
              "    }"
            ]
        FunctionNotFound msg -> error msg
        FunctionIgnored -> "    /* Ignore type inside Array: '" ++ show t ++ "' ??? */\n"
