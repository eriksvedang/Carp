{-# LANGUAGE LambdaCase #-}

module Eval where

import ColorText
import Commands
import Context
import Control.Applicative
import Control.Exception
import Control.Monad.State
import Data.Either (fromRight)
import Data.Foldable (foldlM, foldrM)
import Data.List (foldl', isSuffixOf)
import Data.List.Split (splitOn, splitWhen)
import Data.Maybe (fromJust, fromMaybe, isJust)
import Emit
import qualified Env as E
import EvalError
import Expand
import Forms
import Infer
import Info
import qualified Map
import qualified Meta
import Obj
import Parsing
import Path
import Primitives
import Project
import Qualify
import qualified Set
import System.Exit (ExitCode (..), exitSuccess, exitWith)
import System.Process (readProcessWithExitCode)
import qualified Text.Parsec as Parsec
import TypeError
import Types
import Util
import Prelude hiding (exp, mod)

-- TODO: Formalize "lookup order preference" a bit better and move into
-- the Context module.
data LookupPreference
  = PreferDynamic
  | PreferGlobal
  | PreferLocal [SymPath]
  deriving (Show)

data Resolver
  = ResolveGlobal
  | ResolveLocal

type Evaluator = [XObj] -> IO (Context, Either EvalError XObj)

-- Prefer dynamic bindings
evalDynamic :: Resolver -> Context -> XObj -> IO (Context, Either EvalError XObj)
evalDynamic resolver ctx xobj = eval ctx xobj PreferDynamic resolver

-- Prefer global bindings
evalStatic :: Resolver -> Context -> XObj -> IO (Context, Either EvalError XObj)
evalStatic resolver ctx xobj = eval ctx xobj PreferGlobal resolver

-- | Dynamic (REPL) evaluation of XObj:s (s-expressions)
-- Note: You might find a bunch of code of the following form both here and in
-- macroExpand:
--
-- pure (ctx, do res <- <something>
--               Right <something else with res>)
--
-- This might a little weird to you, and rightfully so. Through the nested do
-- we ensure that an evaluation is forced where it needs to be, since we depend
-- on the state here; eval is inherently stateful (because it carries around
-- the compiler’s context, which might change after each macro expansion), and
-- it gets real weird with laziness. (Note to the note: this code is mostly a
-- remnant of us using StateT, and might not be necessary anymore since we
-- switched to more explicit state-passing.)
eval :: Context -> XObj -> LookupPreference -> Resolver -> IO (Context, Either EvalError XObj)
eval ctx xobj@(XObj o info ty) preference resolver =
  case o of
    Lst body -> eval' body
    Sym spath@(SymPath p n) _ ->
      pure $
        case resolver of
          ResolveGlobal -> unwrapLookup ((tryAllLookups preference) >>= checkStatic)
          ResolveLocal -> unwrapLookup (tryAllLookups preference)
      where
        checkStatic v@(_, Right (XObj (Lst ((XObj obj _ _) : _)) _ _)) =
          if isResolvableStaticObj obj
            then pure (ctx, Left (HasStaticCall xobj info))
            else pure v
        checkStatic v = pure v
        -- all else failed, error.
        unwrapLookup =
          fromMaybe
            (throwErr (SymbolNotFound spath) ctx info)
        -- Try all lookups performs lookups for symbols based on a given
        -- lookup preference.
        tryAllLookups :: LookupPreference -> Maybe (Context, Either EvalError XObj)
        tryAllLookups PreferDynamic = (getDynamic) <|> fullLookup
        tryAllLookups PreferGlobal = (getGlobal spath) <|> fullLookup
        tryAllLookups (PreferLocal shadows) = (if spath `elem` shadows then (getLocal n) else (getDynamic)) <|> fullLookup
        fullLookup = (tryDynamicLookup <|> (if null p then tryInternalLookup spath <|> tryLookup spath else tryLookup spath))
        getDynamic :: Maybe (Context, Either EvalError XObj)
        getDynamic =
          do
            (Binder _ found) <- maybeId (E.findValueBinder (contextGlobalEnv ctx) (SymPath ("Dynamic" : p) n))
            pure (ctx, Right (resolveDef found))
        getGlobal :: SymPath -> Maybe (Context, Either EvalError XObj)
        getGlobal path =
          do
            (Binder meta found) <- maybeId (E.findValueBinder (contextGlobalEnv ctx) path)
            checkPrivate meta found
        tryDynamicLookup :: Maybe (Context, Either EvalError XObj)
        tryDynamicLookup =
          do
            (Binder meta found) <- maybeId (E.searchValueBinder (contextGlobalEnv ctx) (SymPath ("Dynamic" : p) n))
            checkPrivate meta found
        getLocal :: String -> Maybe (Context, Either EvalError XObj)
        getLocal name =
          do
            internal <- contextInternalEnv ctx
            (Binder _ found) <- maybeId (E.getValueBinder internal name)
            pure (ctx, Right (resolveDef found))
        -- TODO: Deprecate this function?
        -- The behavior here is a bit nefarious since it relies on cached
        -- environment parents (it calls `search` on the "internal" binder).
        -- But for now, it seems to be needed for some cases.
        tryInternalLookup :: SymPath -> Maybe (Context, Either EvalError XObj)
        tryInternalLookup path =
          --trace ("Looking for internally " ++ show path) -- ++ show (fmap (fmap E.binders . E.parent) (contextInternalEnv ctx)))
          ( contextInternalEnv ctx
              >>= \e ->
                maybeId (E.searchValueBinder e path)
                  >>= \(Binder meta found) -> checkPrivate meta found
          )
        tryLookup :: SymPath -> Maybe (Context, Either EvalError XObj)
        tryLookup path =
          ( maybeId (E.searchValueBinder (contextGlobalEnv ctx) path)
              >>= \(Binder meta found) -> checkPrivate meta found
          )
            <|> ( (maybeId (E.searchValueBinder (contextGlobalEnv ctx) (SymPath ((contextPath ctx) ++ p) n)))
                    >>= \(Binder meta found) -> checkPrivate meta found
                )
            <|> ( maybeId (lookupBinderInTypeEnv ctx path)
                    >>= \(Binder _ found) -> pure (ctx, Right (resolveDef found))
                )
            <|> ( foldl
                    (<|>)
                    Nothing
                    ( map
                        ( \(SymPath p' n') ->
                            maybeId (E.searchValueBinder (contextGlobalEnv ctx) (SymPath (p' ++ (n' : p)) n))
                              >>= \(Binder meta found) -> checkPrivate meta found
                        )
                        (Set.toList (envUseModules (contextGlobalEnv ctx)))
                    )
                )
        checkPrivate meta found =
          pure $
            if metaIsTrue meta "private"
              then throwErr (PrivateBinding (getPath found)) ctx info
              else (ctx, Right (resolveDef found))
    Arr objs -> do
      (newCtx, evaled) <- foldlM successiveEval (ctx, Right []) objs
      pure
        ( newCtx,
          do
            ok <- evaled
            Right (XObj (Arr ok) info ty)
        )
    StaticArr objs -> do
      (newCtx, evaled) <- foldlM successiveEval (ctx, Right []) objs
      pure
        ( newCtx,
          do
            ok <- evaled
            Right (XObj (StaticArr ok) info ty)
        )
    _ -> do
      (nctx, res) <- annotateWithinContext ctx xobj
      pure $ case res of
        Left e -> (nctx, Left e)
        Right (val, _) -> (nctx, Right val)
  where
    resolveDef (XObj (Lst [XObj DefDynamic _ _, _, value]) _ _) = value
    resolveDef (XObj (Lst [XObj LocalDef _ _, _, value]) _ _) = value
    resolveDef x = x
    eval' form =
      case validate form of
        Left e -> pure (evalError ctx (format e) (xobjInfo xobj))
        Right form' ->
          case form' of
            (IfPat _ _ _ _) -> evaluateIf form'
            (DefnPat _ _ _ _) -> specialCommandDefine ctx xobj
            (DefPat _ _ _) -> specialCommandDefine ctx xobj
            (ThePat _ _ _) -> evaluateThe form'
            (LetPat _ _ _) -> evaluateLet form'
            (FnPat _ _ _) -> evaluateFn form'
            (AppPat (ClosurePat _ _ _) _) -> evaluateClosure form'
            (AppPat (DynamicFnPat _ _ _) _) -> evaluateDynamicFn form'
            (AppPat (MacroPat _ _ _) _) -> evaluateMacro form'
            (AppPat (CommandPat _ _ _) _) -> evaluateCommand form'
            (AppPat (PrimitivePat _ _ _) _) -> evaluatePrimitive form'
            (WithPat _ sym@(SymPat path) forms) -> specialCommandWith ctx sym path forms
            (DoPat _ forms) -> evaluateSideEffects forms
            (WhilePat _ cond body) -> specialCommandWhile ctx cond body
            (SetPat _ iden value) -> specialCommandSet ctx (iden : [value])
            -- This next match is a bit redundant looking at first glance, but
            -- it is necessary to prevent hangs on input such as: `((def foo 2)
            -- 4)`. Ideally, we could perform only *one* static check (the one
            -- we do in eval). But the timing is wrong.
            -- The `def` in the example above initially comes into the
            -- evaluator as a *Sym*, **not** as a `Def` xobj.  So, we need to
            -- discriminate on the result of evaluating the symbol to eagerly
            -- break the evaluation loop, otherwise we will proceed to evaluate
            -- the def form, yielding Unit, and attempt to reevaluate unit
            -- indefinitely on subsequent eval loops.
            -- Importantly, the loop *is only broken on literal nested lists*.
            -- That is, passing a *symbol* that, e.g. resolves to a defn list, won't
            -- break our normal loop.
            (AppPat self@(ListPat (x@(SymPat _) : _)) args) ->
              do
                (_, evald) <- eval ctx x preference ResolveGlobal
                case evald of
                  Left err -> pure (evalError ctx (show err) (xobjInfo xobj))
                  Right x' -> case checkStatic' x' of
                    Right _ -> evaluateApp (self : args)
                    Left er -> pure (evalError ctx (show er) (xobjInfo xobj))
            (AppPat (ListPat _) _) -> evaluateApp form'
            (AppPat (SymPat _) _) -> evaluateApp form'
            [] -> pure (ctx, dynamicNil)
            _ -> pure (throwErr (UnknownForm xobj) ctx (xobjInfo xobj))
    checkStatic' (XObj Def _ _) = Left (HasStaticCall xobj info)
    checkStatic' (XObj (Defn _) _ _) = Left (HasStaticCall xobj info)
    checkStatic' (XObj (Interface _ _) _ _) = Left (HasStaticCall xobj info)
    checkStatic' (XObj (Instantiate _) _ _) = Left (HasStaticCall xobj info)
    checkStatic' (XObj (Deftemplate _) _ _) = Left (HasStaticCall xobj info)
    checkStatic' (XObj (External _) _ _) = Left (HasStaticCall xobj info)
    checkStatic' (XObj (Match _) _ _) = Left (HasStaticCall xobj info)
    checkStatic' (XObj Ref _ _) = Left (HasStaticCall xobj info)
    checkStatic' x' = Right x'
    successiveEval (ctx', acc) x =
      case acc of
        Left _ -> pure (ctx', acc)
        Right l -> do
          (newCtx, evald) <- eval ctx' x preference resolver
          pure $ case evald of
            Right res -> (newCtx, Right (l ++ [res]))
            Left err -> (newCtx, Left err)
    evaluateIf :: Evaluator
    evaluateIf (IfPat _ cond true false) = do
      (newCtx, evd) <- eval ctx cond preference ResolveLocal
      case evd of
        Right cond' ->
          case xobjObj cond' of
            Bol b -> eval newCtx (if b then true else false) preference ResolveLocal
            _ ->
              pure (throwErr (IfContainsNonBool cond) ctx (xobjInfo cond))
        Left e -> pure (newCtx, Left e)
    evaluateIf _ = pure (evalError ctx (format (GenericMalformed xobj)) (xobjInfo xobj))
    evaluateThe :: Evaluator
    evaluateThe (ThePat the t value) = do
      (newCtx, evaledValue) <- expandAll (evalDynamic ResolveLocal) ctx value -- TODO: Why expand all here?
      pure
        ( newCtx,
          do
            okValue <- evaledValue
            Right (XObj (Lst [the, t, okValue]) info ty)
        )
    evaluateThe _ = pure (evalError ctx (format (GenericMalformed xobj)) (xobjInfo xobj))
    evaluateLet :: Evaluator
    evaluateLet (LetPat _ (ArrPat bindings) body) = do
      let binds = unwrapVar (pairwise bindings) []
          ni = Env Map.empty (contextInternalEnv ctx) Nothing Set.empty InternalEnv 0
      eitherCtx <- foldrM successiveEval' (Right (replaceInternalEnv ctx ni)) binds
      case eitherCtx of
        Left err -> pure (ctx, Left err)
        Right newCtx -> do
          (finalCtx, evaledBody) <- eval newCtx body (PreferLocal (map (\(name, _) -> (SymPath [] name)) binds)) ResolveLocal
          let Just e = contextInternalEnv finalCtx
              parentEnv = envParent e
          pure
            ( replaceInternalEnvMaybe finalCtx parentEnv,
              do
                okBody <- evaledBody
                Right okBody
            )
      where
        unwrapVar [] acc = acc
        unwrapVar ((XObj (Sym (SymPath [] x) _) _ _, y) : xs) acc = unwrapVar xs ((x, y) : acc)
        unwrapVar _ _ = error "unwrapvar"
        successiveEval' (n, x) =
          \case
            err@(Left _) -> pure err
            Right ctx' -> do
              -- Bind a reference to the let bind in a recursive
              -- environment. This permits recursion in anonymous functions
              -- in let binds such as:
              --   (let [f (fn [x] (if (= x 1) x (f (dec x))))] (f 10))
              let origin = (contextInternalEnv ctx')
                  recFix = (E.recursive origin (Just "let-rec-env") 0)
                  Right envWithSelf = if isFn x then E.insertX recFix (SymPath [] n) x else Right recFix
                  ctx'' = replaceInternalEnv ctx' envWithSelf
              (newCtx, res) <- eval ctx'' x preference resolver
              case res of
                Right okX ->
                  pure $ Right (fromRight (error "Failed to eval let binding!!") (bindLetDeclaration (newCtx {contextInternalEnv = origin}) n okX))
                Left err -> pure $ Left err
    evaluateLet _ = pure (evalError ctx (format (GenericMalformed xobj)) (xobjInfo xobj))
    evaluateFn :: Evaluator
    evaluateFn (FnPat self args body) = do
      (newCtx, expanded) <- macroExpand ctx body
      pure $
        case expanded of
          Right b ->
            (newCtx, Right (XObj (Closure (XObj (Lst [self, args, b]) info ty) (CCtx newCtx)) info ty))
          Left err -> (ctx, Left err)
    evaluateFn _ = pure (evalError ctx (format (GenericMalformed xobj)) (xobjInfo xobj))
    evaluateClosure :: Evaluator
    evaluateClosure (AppPat (ClosurePat params body c) args) = do
      (newCtx, evaledArgs) <- foldlM successiveEval (ctx, Right []) args
      case evaledArgs of
        Right okArgs -> do
          let newGlobals = (contextGlobalEnv newCtx) <> (contextGlobalEnv c)
              newTypes = TypeEnv $ (getTypeEnv (contextTypeEnv newCtx)) <> (getTypeEnv (contextTypeEnv c))
              updater = replaceHistory' (contextHistory ctx) . replaceGlobalEnv' newGlobals . replaceTypeEnv' newTypes
          (ctx', res) <- apply (updater c) body params okArgs
          pure (replaceGlobalEnv newCtx (contextGlobalEnv ctx'), res)
        Left err -> pure (newCtx, Left err)
    evaluateClosure _ = pure (evalError ctx (format (GenericMalformed xobj)) (xobjInfo xobj))
    evaluateDynamicFn :: Evaluator
    evaluateDynamicFn (AppPat (DynamicFnPat _ params body) args) = do
      (newCtx, evaledArgs) <- foldlM successiveEval (ctx, Right []) args
      case evaledArgs of
        Right okArgs -> apply newCtx body params okArgs
        Left err -> pure (newCtx, Left err)
    evaluateDynamicFn _ = pure (evalError ctx (format (GenericMalformed xobj)) (xobjInfo xobj))
    evaluateMacro :: Evaluator
    evaluateMacro (AppPat (MacroPat _ params body) args) = do
      (ctx', res) <- apply ctx body params args
      case res of
        Right xobj' -> macroExpand ctx' xobj'
        Left _ -> pure (ctx, res)
    evaluateMacro _ = pure (evalError ctx (format (GenericMalformed xobj)) (xobjInfo xobj))
    evaluateCommand :: Evaluator
    evaluateCommand (AppPat (CommandPat (NullaryCommandFunction nullary) _ _) []) =
      nullary ctx
    evaluateCommand (AppPat (CommandPat (UnaryCommandFunction unary) _ _) [x]) = do
      (c, evaledArgs) <- foldlM successiveEval (ctx, Right []) [x]
      case evaledArgs of
        Right args -> let [x'] = take 1 args in unary c x'
        Left err -> pure (ctx, Left err)
    evaluateCommand (AppPat (CommandPat (BinaryCommandFunction binary) _ _) [x, y]) = do
      (c, evaledArgs) <- foldlM successiveEval (ctx, Right []) [x, y]
      case evaledArgs of
        Right args -> let [x', y'] = take 2 args in binary c x' y'
        Left err -> pure (ctx, Left err)
    evaluateCommand (AppPat (CommandPat (TernaryCommandFunction ternary) _ _) [x, y, z]) = do
      (c, evaledArgs) <- foldlM successiveEval (ctx, Right []) [x, y, z]
      case evaledArgs of
        Right args' -> let [x', y', z'] = take 3 args' in ternary c x' y' z'
        Left err -> pure (ctx, Left err)
    evaluateCommand (AppPat (CommandPat (VariadicCommandFunction variadic) _ _) args) = do
      (c, evaledArgs) <- foldlM successiveEval (ctx, Right []) args
      case evaledArgs of
        Right args' -> variadic c args'
        Left err -> pure (ctx, Left err)
    -- Should be caught during validation
    evaluateCommand (AppPat (CommandPat _ _ _) _) =
      pure (evalError ctx (format (GenericMalformed xobj)) (xobjInfo xobj))
    evaluateCommand _ = pure (evalError ctx (format (GenericMalformed xobj)) (xobjInfo xobj))
    evaluatePrimitive :: Evaluator
    evaluatePrimitive (AppPat p@(PrimitivePat (NullaryPrimitive nullary) _ _) []) =
      nullary p ctx
    evaluatePrimitive (AppPat p@(PrimitivePat (UnaryPrimitive unary) _ _) [x]) = do
      unary p ctx x
    evaluatePrimitive (AppPat p@(PrimitivePat (BinaryPrimitive binary) _ _) [x, y]) = do
      binary p ctx x y
    evaluatePrimitive (AppPat p@(PrimitivePat (TernaryPrimitive ternary) _ _) [x, y, z]) = do
      ternary p ctx x y z
    evaluatePrimitive (AppPat p@(PrimitivePat (QuaternaryPrimitive quaternary) _ _) [x, y, z, w]) = do
      quaternary p ctx x y z w
    evaluatePrimitive (AppPat p@(PrimitivePat (VariadicPrimitive variadic) _ _) args) = do
      variadic p ctx args
    -- Should be caught during validation
    evaluatePrimitive (AppPat (PrimitivePat _ _ _) _) =
      pure (evalError ctx (format (GenericMalformed xobj)) (xobjInfo xobj))
    evaluatePrimitive _ = pure (evalError ctx (format (GenericMalformed xobj)) (xobjInfo xobj))
    evaluateApp :: Evaluator
    evaluateApp (AppPat f' args) =
      case f' of
        l@(ListPat _) -> go l ResolveLocal
        sym@(SymPat _) -> go sym resolver
        _ -> pure (evalError ctx (format (GenericMalformed xobj)) (xobjInfo xobj))
      where
        go x resolve =
          do
            (newCtx, f) <- eval ctx x preference resolve
            case f of
              Right fun -> do
                (newCtx', res) <- eval (pushFrame newCtx xobj) (XObj (Lst (fun : args)) (xobjInfo x) (xobjTy x)) preference ResolveLocal
                pure (popFrame newCtx', res)
              x' -> pure (newCtx, x')
    evaluateApp _ = pure (evalError ctx (format (GenericMalformed xobj)) (xobjInfo xobj))
    evaluateSideEffects :: Evaluator
    evaluateSideEffects forms = do
      foldlM successiveEval' (ctx, dynamicNil) forms
      where
        successiveEval' (ctx', acc) x =
          case acc of
            err@(Left _) -> pure (ctx', err)
            Right _ -> eval ctx' x preference resolver

macroExpand :: Context -> XObj -> IO (Context, Either EvalError XObj)
macroExpand ctx xobj =
  case xobj of
    XObj (Arr objs) i t -> do
      (newCtx, expanded) <- foldlM successiveExpand (ctx, Right []) objs
      pure
        ( newCtx,
          do
            ok <- expanded
            Right (XObj (Arr ok) i t)
        )
    XObj (StaticArr objs) i t -> do
      (newCtx, expanded) <- foldlM successiveExpand (ctx, Right []) objs
      pure
        ( newCtx,
          do
            ok <- expanded
            Right (XObj (StaticArr ok) i t)
        )
    XObj (Lst (XObj (Sym (SymPath [] "defmodule") _) _ _ : _)) _ _ ->
      pure (ctx, Right xobj)
    XObj (Lst [XObj (Sym (SymPath [] "quote") _) _ _, _]) _ _ ->
      pure (ctx, Right xobj)
    XObj (Lst [XObj (Lst (XObj Macro _ _ : _)) _ _]) _ _ -> evalDynamic ResolveLocal ctx xobj
    XObj (Lst (x@(XObj (Sym _ _) _ _) : args)) i t -> do
      (_, f) <- evalDynamic ResolveLocal ctx x
      case f of
        Right m@(XObj (Lst (XObj Macro _ _ : _)) _ _) -> do
          (newCtx', res) <- evalDynamic ResolveLocal ctx (XObj (Lst (m : args)) i t)
          pure (newCtx', res)
        _ -> do
          (newCtx, expanded) <- foldlM successiveExpand (ctx, Right []) args
          pure
            ( newCtx,
              do
                ok <- expanded
                Right (XObj (Lst (x : ok)) i t)
            )
    XObj (Lst objs) i t -> do
      (newCtx, expanded) <- foldlM successiveExpand (ctx, Right []) objs
      pure
        ( newCtx,
          do
            ok <- expanded
            Right (XObj (Lst ok) i t)
        )
    _ -> pure (ctx, Right xobj)
  where
    successiveExpand (ctx', acc) x =
      case acc of
        Left _ -> pure (ctx', acc)
        Right l -> do
          (newCtx, expanded) <- macroExpand ctx' x
          pure $ case expanded of
            Right res -> (newCtx, Right (l ++ [res]))
            Left err -> (newCtx, Left err)

apply :: Context -> XObj -> [XObj] -> [XObj] -> IO (Context, Either EvalError XObj)
apply ctx@Context {contextInternalEnv = internal} body params args =
  let allParams = map getName params
   in case splitWhen (":rest" ==) allParams of
        [a, b] -> callWith a b
        [a] -> callWith a []
        _ ->
          pure (throwErr (MacroBadArgumentSplit allParams) ctx Nothing)
  where
    callWith proper rest = do
      let n = length proper
          insideEnv = Env Map.empty internal Nothing Set.empty InternalEnv 0
          insideEnv' =
            foldl'
              (\e (p, x) -> fromRight (error "Couldn't add local def ") (E.insertX e (SymPath [] p) (toLocalDef p x)))
              insideEnv
              (zip proper (take n args))
          insideEnv'' =
            if null rest
              then insideEnv'
              else
                fromRight
                  (error "couldn't insert into inside env")
                  ( E.insertX
                      insideEnv'
                      (SymPath [] (head rest))
                      (XObj (Lst (drop n args)) Nothing Nothing)
                  )
          binds = if null rest then proper else proper ++ [(head rest)]
      (c, r) <- (eval (replaceInternalEnv ctx insideEnv'') body (PreferLocal (map (\x -> (SymPath [] x)) binds)) ResolveLocal)
      pure (c {contextInternalEnv = internal}, r)

-- | Parses a string and then converts the resulting forms to commands, which are evaluated in order.
executeString :: Bool -> Bool -> Context -> String -> String -> IO Context
executeString = executeStringAtLine 1

executeStringAtLine :: Int -> Bool -> Bool -> Context -> String -> String -> IO Context
executeStringAtLine line doCatch printResult ctx input fileName =
  if doCatch then catch exec (catcher ctx) else exec
  where
    exec = case parseAtLine line input fileName of
      Left parseError ->
        let sourcePos = Parsec.errorPos parseError
            parseErrorXObj =
              XObj
                (Lst [])
                ( Just
                    dummyInfo
                      { infoFile = fileName,
                        infoLine = Parsec.sourceLine sourcePos,
                        infoColumn = Parsec.sourceColumn sourcePos
                      }
                )
                Nothing
         in do
              _ <- liftIO $ treatErr ctx (replaceChars (Map.fromList [('\n', " ")]) (show parseError)) parseErrorXObj
              pure ctx
      Right xobjs -> do
        (res, ctx') <-
          foldM
            interactiveFolder
            (XObj (Lst []) (Just dummyInfo) (Just UnitTy), ctx)
            xobjs
        when
          (printResult && xobjTy res /= Just UnitTy)
          (putStrLnWithColor Yellow ("=> " ++ pretty res))
        pure ctx'
    interactiveFolder (_, context) =
      executeCommand context
    treatErr ctx' e xobj = do
      let fppl = projectFilePathPrintLength (contextProj ctx')
      case contextExecMode ctx' of
        Check -> putStrLn (machineReadableInfoFromXObj fppl xobj ++ " " ++ e)
        _ -> emitErrorWithLabel "PARSE ERROR" e
      throw CancelEvaluationException

-- | Used by functions that has a series of forms to evaluate and need to fold over them (producing a new Context in the end)
folder :: Context -> XObj -> IO Context
folder context xobj = do
  (_, ctx) <- executeCommand context xobj
  pure ctx

-- | Take a repl command and execute it.
executeCommand :: Context -> XObj -> IO (XObj, Context)
executeCommand ctx@(Context env _ _ _ _ _ _ _) xobj =
  do
    when (isJust (envModuleName env)) $
      error ("Global env module name is " ++ fromJust (envModuleName env) ++ " (should be Nothing).")
    -- The s-expression command is a special case that prefers global/static bindings over dynamic bindings
    -- when given a naked binding (no path) as an argument; (s-expr inc)
    (newCtx, result) <- if xobjIsSexp xobj then evalStatic ResolveGlobal ctx xobj else evalDynamic ResolveGlobal ctx xobj
    case result of
      Left e@EvalError {} -> do
        reportExecutionError newCtx (show e)
        pure (xobj, newCtx)
      -- special case: calling something static at the repl
      Right (XObj (Lst (XObj (Lst (XObj (Defn _) _ _ : (XObj (Sym (SymPath [] "main") _) _ _) : _)) _ _ : _)) _ _) ->
        executeCommand newCtx (withBuildAndRun (XObj (Lst []) (Just dummyInfo) Nothing))
      Left (HasStaticCall _ _) ->
        callFromRepl newCtx xobj
      Right res -> pure (res, newCtx)
  where
    callFromRepl newCtx xobj' = do
      (nc, r) <- annotateWithinContext newCtx xobj'
      case r of
        Right (ann, deps) -> do
          ctxWithDeps <- liftIO $ foldM (define True) nc (map Qualified deps)
          executeCommand ctxWithDeps (withBuildAndRun (buildMainFunction ann))
        Left err -> do
          reportExecutionError nc (show err)
          pure (xobj', nc)
    withBuildAndRun xobj' =
      XObj
        ( Lst
            [ XObj Do (Just dummyInfo) Nothing,
              xobj',
              XObj
                (Lst [XObj (Sym (SymPath [] "build") Symbol) (Just dummyInfo) Nothing, trueXObj])
                (Just dummyInfo)
                Nothing,
              XObj
                (Lst [XObj (Sym (SymPath [] "run") Symbol) (Just dummyInfo) Nothing])
                (Just dummyInfo)
                Nothing,
              (XObj (Lst []) (Just dummyInfo) (Just UnitTy))
            ]
        )
        (Just dummyInfo)
        Nothing
    xobjIsSexp (XObj (Lst (XObj (Sym (SymPath [] "s-expr") Symbol) _ _ : _)) _ _) = True
    xobjIsSexp _ = False

reportExecutionError :: Context -> String -> IO ()
reportExecutionError ctx errorMessage =
  case contextExecMode ctx of
    Check -> putStrLn errorMessage
    _ ->
      do
        emitErrorBare errorMessage
        throw CancelEvaluationException

-- | Decides what to do when the evaluation fails for some reason.
catcher :: Context -> CarpException -> IO Context
catcher ctx exception =
  case exception of
    (ShellOutException message rc) -> emitErrorWithLabel "RUNTIME ERROR" message >> stop rc
    CancelEvaluationException -> stop 1
    EvalException err -> emitError (show err) >> stop 1
  where
    stop rc =
      case contextExecMode ctx of
        Repl -> pure ctx
        Build -> exitWith (ExitFailure rc)
        Install _ -> exitWith (ExitFailure rc)
        BuildAndRun -> exitWith (ExitFailure rc)
        Check -> exitSuccess

specialCommandWith :: Context -> XObj -> SymPath -> [XObj] -> IO (Context, Either EvalError XObj)
specialCommandWith ctx _ path forms = do
  let Just env = contextInternalEnv ctx <|> maybeId (innermostModuleEnv ctx) <|> Just (contextGlobalEnv ctx)
      useThese = envUseModules env
      env' = env {envUseModules = Set.insert path useThese}
      ctx' = replaceGlobalEnv ctx env'
  ctxAfter <- liftIO $ foldM folder ctx' forms
  let Just envAfter = contextInternalEnv ctxAfter <|> maybeId (innermostModuleEnv ctxAfter) <|> Just (contextGlobalEnv ctxAfter)
      -- undo ALL use:s made inside the 'with'.
      ctxAfter' = replaceGlobalEnv ctx (envAfter {envUseModules = useThese})
  pure (ctxAfter', dynamicNil)

specialCommandDefine :: Context -> XObj -> IO (Context, Either EvalError XObj)
specialCommandDefine ctx xobj =
  do
    (newCtx, result) <- annotateWithinContext ctx xobj
    case result of
      Right (annXObj, annDeps) ->
        do
          ctxWithDeps <- liftIO $ foldM (define True) newCtx (map Qualified annDeps)
          ctxWithDef <- liftIO $ define False ctxWithDeps (Qualified annXObj)
          pure (ctxWithDef, dynamicNil)
      Left err ->
        pure (ctx, Left err)

specialCommandWhile :: Context -> XObj -> XObj -> IO (Context, Either EvalError XObj)
specialCommandWhile ctx cond body = do
  (newCtx, evd) <- evalDynamic ResolveLocal ctx cond
  case evd of
    Right c ->
      case xobjObj c of
        Bol b ->
          if b
            then do
              (newCtx', _) <- evalDynamic ResolveLocal newCtx body
              specialCommandWhile newCtx' cond body
            else pure (newCtx, dynamicNil)
        _ ->
          pure (throwErr (WhileContainsNonBool c) ctx (xobjInfo c))
    Left e -> pure (newCtx, Left e)

getSigFromDefnOrDef :: Context -> XObj -> Either EvalError (Maybe (Ty, XObj))
getSigFromDefnOrDef ctx xobj =
  let pathStrings = contextPath ctx
      globalEnv = contextGlobalEnv ctx
      fppl = projectFilePathPrintLength (contextProj ctx)
      path = getPath xobj
      fullPath = case path of
        (SymPath [] _) -> consPath pathStrings path
        (SymPath _ _) -> path
      metaData = either (const emptyMeta) id (E.lookupMeta globalEnv fullPath)
   in case Meta.get "sig" metaData of
        Just foundSignature ->
          case xobjToTy foundSignature of
            Just t ->
              let sigToken = XObj (Sym (SymPath [] "sig") Symbol) Nothing Nothing
                  nameToken = XObj (Sym (SymPath [] (getName xobj)) Symbol) Nothing Nothing
                  recreatedSigForm = XObj (Lst [sigToken, nameToken, foundSignature]) Nothing (Just MacroTy)
               in Right (Just (t, recreatedSigForm))
            Nothing -> Left (EvalError ("Can't use '" ++ pretty foundSignature ++ "' as a type signature") (contextHistory ctx) fppl (xobjInfo xobj))
        Nothing -> Right Nothing

annotateWithinContext :: Context -> XObj -> IO (Context, Either EvalError (XObj, [XObj]))
annotateWithinContext ctx xobj = do
  let globalEnv = contextGlobalEnv ctx
      typeEnv = contextTypeEnv ctx
      sig = getSigFromDefnOrDef ctx xobj
      fppl = projectFilePathPrintLength (contextProj ctx)
  case sig of
    Left err -> pure (ctx, Left err)
    Right okSig -> do
      (_, expansionResult) <- expandAll (evalDynamic ResolveLocal) ctx xobj
      case expansionResult of
        Left err -> pure (ctx, Left err)
        Right expanded ->
          let xobjFullSymbols = qualify ctx expanded
           in case xobjFullSymbols of
                Left err -> pure (evalError ctx (show err) (xobjInfo xobj))
                Right xs ->
                  case annotate typeEnv globalEnv xs okSig of
                    Left err ->
                      -- TODO: Replace this with a single call to evalError (which already checks the execution mode)
                      case contextExecMode ctx of
                        Check -> pure (evalError ctx (joinLines (machineReadableErrorStrings fppl err)) Nothing)
                        _ -> pure (evalError ctx (show err) (xobjInfo xobj))
                    Right ok -> pure (ctx, Right ok)

primitiveDefmodule :: VariadicPrimitiveCallback
primitiveDefmodule xobj ctx@(Context env i tenv pathStrings _ _ _ _) (XObj (Sym (SymPath [] moduleName) _) si _ : innerExpressions) =
  -- N.B. The `envParent` rewrite at the end of this line is important!
  -- lookups delve into parent envs by default, which is normally what we want, but in this case it leads to problems
  -- when submodules happen to share a name with an existing module or type at the global level.
  either (const (defineNewModule emptyMeta)) updateExistingModule (E.searchValueBinder ((fromRight env (E.getInnerEnv env pathStrings)) {envParent = Nothing}) (SymPath [] moduleName))
    >>= defineModuleBindings
    >>= \(newCtx, result) ->
      let updater c = (c {contextInternalEnv = (E.parent =<< contextInternalEnv c)})
       in case result of
            Left err -> pure (newCtx, Left err)
            Right _ -> pure (updater (popModulePath newCtx), dynamicNil)
  where
    --------------------------------------------------------------------------------
    -- Update an existing module by modifying its environment parents and updating the current context path.
    updateExistingModule :: Binder -> IO (Context, Either EvalError XObj)
    updateExistingModule (Binder _ (XObj (Mod innerEnv _) _ _)) =
      let updateContext =
            replacePath' (contextPath ctx ++ [moduleName])
              . replaceInternalEnv' (innerEnv {envParent = i})
       in pure (updateContext ctx, dynamicNil)
    updateExistingModule (Binder meta (XObj (Lst [XObj MetaStub _ _, _]) _ _)) =
      defineNewModule meta
    updateExistingModule _ =
      pure (throwErr (ModuleRedefinition moduleName) ctx (xobjInfo xobj))
    --------------------------------------------------------------------------------
    -- Define a brand new module with a context's current environments as its parents.
    defineNewModule :: MetaData -> IO (Context, Either EvalError XObj)
    defineNewModule meta =
      pure (fromRight ctx (updater ctx), dynamicNil)
      where
        moduleDefs = E.new (Just (fromRight env (E.getInnerEnv env pathStrings))) (Just moduleName)
        moduleTypes = E.new (Just tenv) (Just moduleName)
        newModule = XObj (Mod moduleDefs moduleTypes) si (Just ModuleTy)
        updater = \c ->
          insertInGlobalEnv' (markQualified (SymPath pathStrings moduleName)) (Binder meta newModule) c
            >>= pure . replaceInternalEnv' (moduleDefs {envParent = i})
            >>= pure . replacePath' (contextPath ctx ++ [moduleName])
    --------------------------------------------------------------------------------
    -- Define bindings for the module.
    defineModuleBindings :: (Context, Either EvalError XObj) -> IO (Context, Either EvalError XObj)
    defineModuleBindings (context, Left e) = pure (context, Left e)
    defineModuleBindings (context, _) =
      foldM step (context, dynamicNil) innerExpressions
    step :: (Context, Either EvalError XObj) -> XObj -> IO (Context, Either EvalError XObj)
    step (ctx', Left e) _ = pure (ctx', Left e)
    step (ctx', Right _) expressions =
      macroExpand ctx' expressions
        >>= \(ctx'', res) -> case res of
          Left err -> pure (ctx'', Left err)
          Right r -> evalDynamic ResolveLocal ctx'' r
primitiveDefmodule _ ctx (x : _) =
  pure (throwErr (DefmoduleContainsNonSymbol x) ctx (xobjInfo x))
primitiveDefmodule xobj ctx [] =
  pure (throwErr DefmoduleNoArgs ctx (xobjInfo xobj))

-- | "NORMAL" COMMANDS (just like the ones in Command.hs, but these need access to 'eval', etc.)

-- | Command for loading a Carp file.
commandLoad :: VariadicCommandCallback
commandLoad ctx [xobj@(XObj (Str path) i _), XObj (Str toLoad) _ _] =
  loadInternal ctx xobj path i (Just toLoad) DoesReload
commandLoad ctx [XObj (Str _) _ _, x] =
  pure $ throwErr (loadInvalidArgs [x]) ctx (xobjInfo x)
commandLoad ctx [x, _] =
  pure $ throwErr (loadInvalidArgs [x]) ctx (xobjInfo x)
commandLoad ctx [xobj@(XObj (Str path) i _)] =
  loadInternal ctx xobj path i Nothing DoesReload
commandLoad ctx x =
  pure $ throwErr (loadInvalidArgs x) ctx Nothing

commandLoadOnce :: VariadicCommandCallback
commandLoadOnce ctx [xobj@(XObj (Str path) i _), XObj (Str toLoad) _ _] =
  loadInternal ctx xobj path i (Just toLoad) Frozen
commandLoadOnce ctx [XObj (Str _) _ _, x] =
  pure $ throwErr (loadOnceInvalidArgs [x]) ctx (xobjInfo x)
commandLoadOnce ctx [x, _] =
  pure $ throwErr (loadOnceInvalidArgs [x]) ctx (xobjInfo x)
commandLoadOnce ctx [xobj@(XObj (Str path) i _)] =
  loadInternal ctx xobj path i Nothing Frozen
commandLoadOnce ctx x =
  pure $ throwErr (loadOnceInvalidArgs x) ctx Nothing

loadInternal :: Context -> XObj -> String -> Maybe Info -> Maybe String -> ReloadMode -> IO (Context, Either EvalError XObj)
loadInternal ctx xobj path i fileToLoad reloadMode = do
  let proj = contextProj ctx
  libDir <- liftIO $ cachePath $ projectLibDir proj
  let relativeTo = case i of
        Just ii ->
          case infoFile ii of
            "REPL" -> "."
            file -> takeDirectory file
        Nothing -> "."
      carpDir = projectCarpDir proj
      fullSearchPaths =
        path :
        (relativeTo </> path) :
        map (</> path) (projectCarpSearchPaths proj) -- the path from the file that contains the '(load)', or the current directory if not loading from a file (e.g. the repl)
          ++ [carpDir </> "core" </> path] -- user defined search paths
          ++ [libDir </> path]
      firstM _ [] = pure Nothing
      firstM p (x : xs) = do
        q <- p x
        if q
          then pure $ Just x
          else firstM p xs
  existingPath <- liftIO $ firstM doesFileExist fullSearchPaths
  case existingPath of
    Nothing ->
      if '@' `elem` path
        then tryInstall path
        else pure $ invalidPath ctx path
    Just firstPathFound ->
      do
        canonicalPath <- liftIO (canonicalizePath firstPathFound)
        fileThatLoads <- liftIO (canonicalizePath $ maybe "" infoFile i)
        if canonicalPath == fileThatLoads
          then pure $ cantLoadSelf ctx path
          else do
            let alreadyLoaded = projectAlreadyLoaded proj ++ frozenPaths proj
            if canonicalPath `elem` alreadyLoaded
              then pure (ctx, dynamicNil)
              else do
                contents <- liftIO $ slurp canonicalPath
                let files = projectFiles proj
                    files' =
                      if canonicalPath `elem` map fst files
                        then files
                        else files ++ [(canonicalPath, reloadMode)]
                    prevStack = projectLoadStack proj
                    proj' =
                      proj
                        { projectFiles = files',
                          projectAlreadyLoaded = canonicalPath : alreadyLoaded,
                          projectLoadStack = canonicalPath : prevStack
                        }
                newCtx <- liftIO $ executeString True False (replaceProject ctx proj') contents canonicalPath
                pure (replaceProject newCtx (contextProj newCtx) {projectLoadStack = prevStack}, dynamicNil)
  where
    frozenPaths proj =
      if projectForceReload proj
        then [] -- No paths are Frozen when the "force reload" project setting is true.
        else map fst $ filter (isFrozen . snd) (projectFiles proj)
    isFrozen Frozen = True
    isFrozen _ = False
    invalidPath ctx' path' =
      throwErr (LoadFileNotFound path') ctx' (xobjInfo xobj)
    invalidPathWith ctx' path' stderr cleanup cleanupPath = do
      _ <- liftIO $ when cleanup (removeDirectoryRecursive cleanupPath)
      pure $
        throwErr (LoadGitFailure path' stderr) ctx' (xobjInfo xobj)
    replaceC _ _ [] = []
    replaceC c s (a : b) = if a == c then s ++ replaceC c s b else a : replaceC c s b
    cantLoadSelf ctx' path' =
      throwErr (LoadRecursiveLoad path') ctx' (xobjInfo xobj)
    tryInstall path' =
      let split = splitOn "@" path'
       in tryInstallWithCheckout (joinWith "@" (init split)) (last split)
    fromURL url =
      let split = splitOn "/" (replaceC ':' "_COLON_" url)
          first = head split
       in if first `elem` ["https_COLON_", "http_COLON_"]
            then joinWith "/" (tail (tail split))
            else
              if '@' `elem` first
                then joinWith "/" (joinWith "@" (tail (splitOn "@" first)) : tail split)
                else url
    tryInstallWithCheckout path' toCheckout = do
      let proj = contextProj ctx
      fpath <- liftIO $ cachePath $ projectLibDir proj </> fromURL path' </> toCheckout
      cur <- liftIO getCurrentDirectory
      pathExists <- liftIO $ doesPathExist fpath
      let cleanup = not pathExists
      _ <- liftIO $ createDirectoryIfMissing True fpath
      _ <- liftIO $ setCurrentDirectory fpath
      (_, txt, _) <- liftIO $ readProcessWithExitCode "git" ["rev-parse", "--abbrev-ref=loose", "HEAD"] ""
      if txt == "HEAD\n"
        then do
          _ <- liftIO $ setCurrentDirectory cur
          doGitLoad path' fpath
        else do
          _ <- liftIO $ readProcessWithExitCode "git" ["init"] ""
          _ <- liftIO $ readProcessWithExitCode "git" ["remote", "add", "origin", path'] ""
          (x0, _, stderr0) <- liftIO $ readProcessWithExitCode "git" ["fetch", "--all", "--tags"] ""
          case x0 of
            ExitFailure _ -> do
              _ <- liftIO $ setCurrentDirectory cur
              invalidPathWith ctx path' stderr0 cleanup fpath
            ExitSuccess -> do
              (x1, _, stderr1) <- liftIO $ readProcessWithExitCode "git" ["checkout", toCheckout] ""
              _ <- liftIO $ setCurrentDirectory cur
              case x1 of
                ExitSuccess -> doGitLoad path' fpath
                ExitFailure _ -> invalidPathWith ctx path' stderr1 cleanup fpath
    doGitLoad path' fpath =
      case fileToLoad of
        Just file -> commandLoad ctx [XObj (Str (fpath </> file)) Nothing Nothing]
        Nothing ->
          -- we’re guessing what file to use here
          let fName = last (splitOn "/" path')
              realName' =
                if ".git" `isSuffixOf` fName
                  then take (length fName - 4) fName
                  else fName
              realName =
                if ".carp" `isSuffixOf` realName'
                  then realName'
                  else realName' ++ ".carp"
              fileToLoad' = fpath </> realName
              mainToLoad = fpath </> "main.carp"
           in do
                (newCtx, res) <- commandLoad ctx [XObj (Str fileToLoad') Nothing Nothing]
                case res of
                  ret@(Right _) -> pure (newCtx, ret)
                  Left _ -> commandLoad ctx [XObj (Str mainToLoad) Nothing Nothing]

-- | Load several files in order.
loadFiles :: Context -> [FilePath] -> IO Context
loadFiles = loadFilesExt commandLoad

loadFilesOnce :: Context -> [FilePath] -> IO Context
loadFilesOnce = loadFilesExt commandLoadOnce

loadFilesExt :: VariadicCommandCallback -> Context -> [FilePath] -> IO Context
loadFilesExt loadCmd = foldM load
  where
    load :: Context -> FilePath -> IO Context
    load ctx file = do
      (newCtx, ret) <- loadCmd ctx [XObj (Str file) Nothing Nothing]
      case ret of
        Left err -> throw (EvalException err)
        Right _ -> pure newCtx

-- | Command for reloading all files in the project (= the files that has been loaded before).
commandReload :: NullaryCommandCallback
commandReload ctx = do
  let paths = projectFiles (contextProj ctx)
      f :: Context -> (FilePath, ReloadMode) -> IO Context
      f context (_, Frozen) | not (projectForceReload (contextProj context)) = pure context
      f context (filepath, _) =
        do
          let proj = contextProj context
              alreadyLoaded = projectAlreadyLoaded proj
          if filepath `elem` alreadyLoaded
            then pure context
            else do
              contents <- slurp filepath
              let proj' = proj {projectAlreadyLoaded = filepath : alreadyLoaded}
              executeString False False (replaceProject context proj') contents filepath
  newCtx <- liftIO (foldM f ctx paths)
  pure (newCtx, dynamicNil)

-- | Command for expanding a form and its macros.
commandExpand :: UnaryCommandCallback
commandExpand = macroExpand

-- | This function will show the resulting C code from an expression.
-- | i.e. (Int.+ 2 3) => "_0 = 2 + 3"
commandC :: UnaryCommandCallback
commandC ctx xobj = do
  (newCtx, result) <- expandAll (evalDynamic ResolveLocal) ctx xobj
  case result of
    Left err -> pure (newCtx, Left err)
    Right expanded -> do
      (_, annotated) <- annotateWithinContext newCtx expanded
      case annotated of
        Left err -> pure $ evalError newCtx (show err) (xobjInfo xobj)
        Right (annXObj, annDeps) ->
          do
            let cXObj = printC annXObj
                cDeps = concatMap printC annDeps
                c = cDeps ++ cXObj
            liftIO (putStr c)
            pure (newCtx, dynamicNil)

-- | Helper function for commandC
printC :: XObj -> String
printC xobj =
  case checkForUnresolvedSymbols xobj of
    Left e ->
      strWithColor Red (show e ++ ", can't print resulting code.\n")
    Right _ ->
      strWithColor Green (toC All (Binder emptyMeta xobj))

buildMainFunction :: XObj -> XObj
buildMainFunction xobj =
  XObj
    ( Lst
        [ XObj (Defn Nothing) di Nothing,
          XObj (Sym (SymPath [] "main") Symbol) di Nothing,
          XObj (Arr []) di Nothing,
          XObj
            ( Lst
                [ XObj Do di Nothing,
                  case xobjTy xobj of
                    Nothing -> error "buildmainfunction"
                    Just UnitTy -> xobj
                    Just (RefTy _ _) ->
                      XObj
                        (Lst [XObj (Sym (SymPath [] "println*") Symbol) di Nothing, xobj])
                        di
                        (Just UnitTy)
                    Just _ ->
                      XObj
                        ( Lst
                            [ XObj (Sym (SymPath [] "println*") Symbol) di Nothing,
                              XObj
                                (Lst [XObj Ref di Nothing, xobj])
                                di
                                (Just UnitTy)
                            ]
                        )
                        di
                        (Just UnitTy),
                  XObj (Num IntTy 0) di Nothing
                ]
            )
            di
            Nothing
        ]
    )
    di
    (Just (FuncTy [] UnitTy StaticLifetimeTy))
  where
    di = Just dummyInfo

primitiveDefdynamic :: BinaryPrimitiveCallback
primitiveDefdynamic _ ctx (XObj (Sym (SymPath [] name) _) _ _) value = do
  (newCtx, result) <- evalDynamic ResolveLocal ctx value
  case result of
    Left err -> pure (newCtx, Left err)
    Right evaledBody ->
      dynamicOrMacroWith newCtx (\path -> [XObj DefDynamic Nothing Nothing, XObj (Sym path Symbol) Nothing Nothing, evaledBody]) DynamicTy name value
primitiveDefdynamic _ ctx notName _ =
  pure (throwErr (DefnDynamicInvalidName notName) ctx (xobjInfo notName))

specialCommandSet :: Context -> [XObj] -> IO (Context, Either EvalError XObj)
specialCommandSet ctx [orig@(XObj (Sym path@(SymPath _ _) _) _ _), val] =
  let lookupInternal =
        maybe (Left "") Right (contextInternalEnv ctx)
          >>= \e ->
            unwrapErr (E.searchValueBinder e path)
              >>= \binder -> pure (binder, setInternal, e)
      lookupGlobal =
        Right (contextGlobalEnv ctx)
          >>= \e ->
            unwrapErr (E.searchValueBinder e path)
              >>= \binder -> pure (binder, setGlobal, e)
   in either
        ((const (pure $ (throwErr (SetVarNotFound orig) ctx (xobjInfo orig)))))
        (\(binder', setter', env') -> evalAndSet binder' setter' env')
        (lookupInternal <> lookupGlobal)
  where
    evalAndSet :: Binder -> (Context -> Env -> Either EvalError XObj -> Binder -> IO (Context, Either EvalError XObj)) -> Env -> IO (Context, Either EvalError XObj)
    evalAndSet binder setter env =
      case xobjTy (binderXObj binder) of
        -- don't type check dynamic or untyped bindings
        -- TODO: Figure out why untyped cases are sometimes coming into set!
        Just DynamicTy -> handleUnTyped
        Nothing -> handleUnTyped
        _ ->
          evalDynamic ResolveLocal ctx val
            >>= \(newCtx, result) ->
              case result of
                Right evald -> typeCheckValueAgainstBinder newCtx evald binder >>= \(nctx, typedVal) -> setter nctx env typedVal binder
                left -> pure (newCtx, left)
      where
        handleUnTyped :: IO (Context, Either EvalError XObj)
        handleUnTyped =
          evalDynamic ResolveLocal ctx val
            >>= \(newCtx, result) -> setter newCtx env result binder
    setGlobal :: Context -> Env -> Either EvalError XObj -> Binder -> IO (Context, Either EvalError XObj)
    setGlobal ctx' env value binder =
      pure $ either (failure ctx' orig) (success ctx') value
      where
        success c xo = (replaceGlobalEnv c (setStaticOrDynamicVar path env binder xo), dynamicNil)
    setInternal :: Context -> Env -> Either EvalError XObj -> Binder -> IO (Context, Either EvalError XObj)
    setInternal ctx' env value binder =
      pure $ either (failure ctx' orig) (success ctx') value
      where
        success c xo = (replaceInternalEnv c (setStaticOrDynamicVar path env binder xo), dynamicNil)
specialCommandSet ctx [notName, _] =
  pure (throwErr (SetInvalidVarName notName) ctx (xobjInfo notName))
specialCommandSet ctx args =
  pure (throwErr (setInvalidArgs args) ctx (if null args then Nothing else xobjInfo (head args)))

-- | Convenience method for signifying failure in a given context.
failure :: Context -> XObj -> EvalError -> (Context, Either EvalError a)
failure ctx orig err = evalError ctx (show err) (xobjInfo orig)

-- | Given a context, value XObj and an existing binder, check whether or not
-- the given value has a type matching the binder's in the given context.
typeCheckValueAgainstBinder :: Context -> XObj -> Binder -> IO (Context, Either EvalError XObj)
typeCheckValueAgainstBinder ctx val binder = do
  (ctx', typedValue) <- annotateWithinContext ctx val
  pure $ case typedValue of
    Right (val', _) -> go ctx' binderTy val'
    Left err -> (ctx', Left err)
  where
    path = getPath (binderXObj binder)
    binderTy = xobjTy (binderXObj binder)
    typeErr x = throwErr (SetTypeMismatch path (fromJust (xobjTy x)) (fromJust binderTy)) ctx (xobjInfo x)
    go ctx'' (Just DynamicTy) x = (ctx'', Right x)
    go ctx'' t x@(XObj _ _ t') = if t == t' then (ctx'', Right x) else typeErr x

-- | Sets a variable, checking whether or not it is static or dynamic, and
-- assigns an appropriate type to the variable.
-- Returns a new environment containing the assignment.
setStaticOrDynamicVar :: SymPath -> Env -> Binder -> XObj -> Env
setStaticOrDynamicVar path@(SymPath _ name) env binder value =
  case binder of
    (Binder meta (XObj (Lst (def@(XObj Def _ _) : sym : _)) _ t)) ->
      fromRight env (E.insert env path (Binder meta (XObj (Lst [def, sym, value]) (xobjInfo value) t)))
    (Binder meta (XObj (Lst (defdy@(XObj DefDynamic _ _) : sym : _)) _ _)) ->
      fromRight env (E.insert env path (Binder meta (XObj (Lst [defdy, sym, value]) (xobjInfo value) (Just DynamicTy))))
    (Binder meta (XObj (Lst (lett@(XObj LocalDef _ _) : sym : _)) _ t)) ->
      fromRight (error "FAILED!") (E.replaceInPlace env name (Binder meta (XObj (Lst [lett, sym, value]) (xobjInfo value) t)))
    -- shouldn't happen, errors are thrown at call sites.
    -- TODO: Return an either here to propagate error.
    _ -> env

primitiveEval :: UnaryPrimitiveCallback
primitiveEval _ ctx val = do
  -- primitives don’t evaluate their arguments, so this needs to double-evaluate
  (newCtx, arg) <- evalDynamic ResolveLocal ctx val
  case arg of
    Left err -> pure (newCtx, Left err)
    Right evald -> do
      (newCtx', expanded) <- macroExpand newCtx evald
      case expanded of
        Left err -> pure (newCtx', Left err)
        Right ok -> do
          (finalCtx, res) <- evalDynamic ResolveLocal newCtx' ok
          pure $ case res of
            Left (HasStaticCall x i) -> throwErr (StaticCall x) ctx i
            _ -> (finalCtx, res)

dynamicOrMacro :: Context -> Obj -> Ty -> String -> XObj -> XObj -> IO (Context, Either EvalError XObj)
dynamicOrMacro ctx pat ty name params body = do
  (ctx', exp) <- macroExpand ctx body
  case exp of
    Right expanded ->
      dynamicOrMacroWith ctx' (\path -> [XObj pat Nothing Nothing, XObj (Sym path Symbol) Nothing Nothing, params, expanded]) ty name body
    Left _ -> pure (ctx, exp)

primitiveDefndynamic :: TernaryPrimitiveCallback
primitiveDefndynamic _ ctx (XObj (Sym (SymPath [] name) _) _ _) params body =
  dynamicOrMacro ctx Dynamic DynamicTy name params body
primitiveDefndynamic _ ctx notName _ _ =
  argumentErr ctx "defndynamic" "a name" "first" notName

primitiveDefmacro :: TernaryPrimitiveCallback
primitiveDefmacro _ ctx (XObj (Sym (SymPath [] name) _) _ _) params body =
  dynamicOrMacro ctx Macro MacroTy name params body
primitiveDefmacro _ ctx notName _ _ =
  argumentErr ctx "defmacro" "a name" "first" notName
