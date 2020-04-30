module GenerateConstraints (genConstraints) where

import Data.List (foldl', sort, zipWith4)
import Control.Arrow
import Control.Monad.State
import Data.Maybe (mapMaybe, fromMaybe)
import Data.Set as Set
import Data.List as List
import Data.Map as Map (lookup)
import Debug.Trace (trace)

import Types
import Obj
import Constraints
import Util
import TypeError
import Lookup

-- | Will create a list of type constraints for a form.
genConstraints :: Env -> XObj -> Maybe (Ty, XObj) -> Either TypeError [Constraint]
genConstraints globalEnv root rootSig = fmap sort (gen root)
  where genF xobj args body captures =
         do insideBodyConstraints <- gen body
            xobjType <- toEither (ty xobj) (DefnMissingType xobj)
            bodyType <- toEither (ty body) (ExpressionMissingType xobj)
            let (FuncTy argTys retTy lifetimeTy) = xobjType
                bodyConstr = Constraint retTy bodyType xobj body xobj OrdDefnBody
                argConstrs = zipWith3 (\a b aObj -> Constraint a b aObj xobj xobj OrdArg) (List.map forceTy args) argTys args
                -- The constraint generated by type signatures, like (sig foo (Fn ...)):
                sigConstr = case rootSig of
                              Just (rootSigTy, rootSigXObj) -> [Constraint rootSigTy xobjType rootSigXObj xobj xobj OrdSignatureAnnotation]
                              Nothing -> []
                captureList :: [XObj]
                captureList = Set.toList captures
                capturesConstrs = mapMaybe id
                                  (zipWith (\captureTy captureObj ->
                                                case captureTy of
                                                  RefTy _ refLt ->
                                                    --trace ("Generated constraint between " ++ show lifetimeTy ++ " and " ++ show refLt) $
                                                    Just (Constraint lifetimeTy refLt captureObj xobj xobj OrdCapture)
                                                  _ ->
                                                    --trace ("Did not generate constraint for captured variable " ++ show captureObj) $
                                                    Nothing)
                                      (List.map forceTy captureList)
                                      captureList)
            return (bodyConstr : argConstrs ++ insideBodyConstraints ++ capturesConstrs ++ sigConstr)
        gen xobj =
          case obj xobj of
            Lst lst -> case lst of
                           -- Defn
                           [XObj (Defn captures) _ _, _, XObj (Arr args) _ _, body] ->
                             genF xobj args body (fromMaybe Set.empty captures)

                           -- Fn
                           [XObj (Fn _ captures) _ _, XObj (Arr args) _ _, body] ->
                             genF xobj args body captures

                           -- Def
                           [XObj Def _ _, _, expr] ->
                             do insideExprConstraints <- gen expr
                                xobjType <- toEither (ty xobj) (DefMissingType xobj)
                                exprType <- toEither (ty expr) (ExpressionMissingType xobj)
                                let defConstraint = Constraint xobjType exprType xobj expr xobj OrdDefExpr
                                    sigConstr = case rootSig of
                                                  Just (rootSigTy, rootSigXObj) -> [Constraint rootSigTy xobjType rootSigXObj xobj xobj OrdSignatureAnnotation]
                                                  Nothing -> []
                                return (defConstraint : insideExprConstraints ++ sigConstr)

                           -- Let
                           [XObj Let _ _, XObj (Arr bindings) _ _, body] ->
                             do insideBodyConstraints <- gen body
                                insideBindingsConstraints <- fmap join (mapM gen bindings)
                                bodyType <- toEither (ty body) (ExpressionMissingType body)
                                let Just xobjTy = ty xobj
                                    wholeStatementConstraint = Constraint bodyType xobjTy body xobj xobj OrdLetBody
                                    bindingsConstraints = zipWith (\(symTy, exprTy) (symObj, exprObj) ->
                                                                     Constraint symTy exprTy symObj exprObj xobj OrdLetBind)
                                                                  (List.map (forceTy *** forceTy) (pairwise bindings))
                                                                  (pairwise bindings)
                                return (wholeStatementConstraint : insideBodyConstraints ++
                                        bindingsConstraints ++ insideBindingsConstraints)

                           -- If
                           [XObj If _ _, expr, ifTrue, ifFalse] ->
                             do insideConditionConstraints <- gen expr
                                insideTrueConstraints <- gen ifTrue
                                insideFalseConstraints <- gen ifFalse
                                exprType <- toEither (ty expr) (ExpressionMissingType expr)
                                trueType <- toEither (ty ifTrue) (ExpressionMissingType ifTrue)
                                falseType <- toEither (ty ifFalse) (ExpressionMissingType ifFalse)
                                let expected = XObj (Sym (SymPath [] "Condition in if value") Symbol) (info expr) (Just BoolTy)
                                let lol = XObj (Sym (SymPath [] "lol") Symbol) (info expr) (Just BoolTy)
                                    conditionConstraint = Constraint exprType BoolTy expr expected xobj OrdIfCondition
                                    sameReturnConstraint = Constraint trueType falseType ifTrue ifFalse xobj OrdIfReturn
                                    Just t = ty xobj
                                    wholeStatementConstraint = Constraint trueType t ifTrue xobj xobj OrdIfWhole
                                return (conditionConstraint : sameReturnConstraint :
                                        wholeStatementConstraint : insideConditionConstraints ++
                                        insideTrueConstraints ++ insideFalseConstraints)

                           -- Match
                           XObj (Match matchMode) _ _ : expr : cases ->
                             do insideExprConstraints <- gen expr
                                casesLhsConstraints <- fmap join (mapM (genConstraintsForCaseMatcher matchMode . fst) (pairwise cases))
                                casesRhsConstraints <- fmap join (mapM (gen . snd) (pairwise cases))
                                exprType <- toEither (ty expr) (ExpressionMissingType expr)
                                xobjType <- toEither (ty xobj) (DefMissingType xobj)

                                let
                                  -- Each case rhs should have the same return type as the whole match form:
                                  mkRetConstr x@(XObj _ _ (Just t)) = Just (Constraint t xobjType x xobj xobj OrdArg) -- | TODO: Ord
                                  mkRetConstr _ = Nothing
                                  returnConstraints = mapMaybe (\(_, rhs) -> mkRetConstr rhs) (pairwise cases)

                                  -- Each case lhs should have the same type as the expression matching on
                                  mkExprConstr x@(XObj _ _ (Just t)) = Just (Constraint (wrapTyInRefIfMatchingRef t) exprType x expr xobj OrdArg) -- | TODO: Ord
                                  mkExprConstr _ = Nothing
                                  exprConstraints = mapMaybe (\(lhs, _) -> mkExprConstr lhs) (pairwise cases)

                                  -- Constraints for the variables in the left side of each matching case,
                                  -- like the 'r'/'g'/'b' in (match col (RGB r g b) ...) being constrained to Int.
                                  -- casesLhsConstraints = concatMap (genLhsConstraintsInCase typeEnv exprType) (map fst (pairwise cases))

                                  -- exprConstraint =
                                  --   -- | TODO: Only guess if there isn't already a type set on the expression!
                                  --   case guessExprType typeEnv cases of
                                  --     Just guessedExprTy ->
                                  --       let expected = XObj (Sym (SymPath [] "Expression in match-statement") Symbol)
                                  --                      (info expr) (Just guessedExprTy)
                                  --       in  [Constraint exprType guessedExprTy expr expected OrdIfCondition] -- | TODO: Ord
                                  --     Nothing ->
                                  --       []

                                return (insideExprConstraints ++
                                        casesLhsConstraints ++
                                        casesRhsConstraints ++
                                        returnConstraints ++
                                        exprConstraints)

                                  where wrapTyInRefIfMatchingRef t =
                                          case matchMode of
                                            MatchValue -> t
                                            MatchRef -> RefTy t (VarTy "whatever")

                           -- While
                           [XObj While _ _, expr, body] ->
                             do insideConditionConstraints <- gen expr
                                insideBodyConstraints <- gen body
                                exprType <- toEither (ty expr) (ExpressionMissingType expr)
                                bodyType <- toEither (ty body) (ExpressionMissingType body)
                                let expectedCond = XObj (Sym (SymPath [] "Condition in while-expression") Symbol) (info expr) (Just BoolTy)
                                    expectedBody = XObj (Sym (SymPath [] "Body in while-expression") Symbol) (info xobj) (Just UnitTy)
                                    conditionConstraint = Constraint exprType BoolTy expr expectedCond xobj OrdWhileCondition
                                    wholeStatementConstraint = Constraint bodyType UnitTy body expectedBody xobj OrdWhileBody
                                return (conditionConstraint : wholeStatementConstraint :
                                        insideConditionConstraints ++ insideBodyConstraints)

                           -- Do
                           XObj Do _ _ : expressions ->
                             case expressions of
                               [] -> Left (NoStatementsInDo xobj)
                               _ -> let lastExpr = last expressions
                                    in do insideExpressionsConstraints <- fmap join (mapM gen expressions)
                                          xobjType <- toEither (ty xobj) (DefMissingType xobj)
                                          lastExprType <- toEither (ty lastExpr) (ExpressionMissingType xobj)
                                          let retConstraint = Constraint xobjType lastExprType xobj lastExpr xobj OrdDoReturn
                                              must = XObj (Sym (SymPath [] "Statement in do-expression") Symbol) (info xobj) (Just UnitTy)
                                              mkConstr x@(XObj _ _ (Just t)) = Just (Constraint t UnitTy x must xobj OrdDoStatement)
                                              mkConstr _ = Nothing
                                              expressionsShouldReturnUnit = mapMaybe mkConstr (init expressions)
                                          return (retConstraint : insideExpressionsConstraints ++ expressionsShouldReturnUnit)

                           -- Address
                           [XObj Address _ _, value] ->
                             gen value

                           -- Set!
                           [XObj SetBang _ _, variable, value] ->
                             do insideValueConstraints <- gen value
                                insideVariableConstraints <- gen variable
                                variableType <- toEither (ty variable) (ExpressionMissingType variable)
                                valueType <- toEither (ty value) (ExpressionMissingType value)
                                let sameTypeConstraint = Constraint variableType valueType variable value xobj OrdSetBang
                                return (sameTypeConstraint : insideValueConstraints ++ insideVariableConstraints)

                           -- The
                           [XObj The _ _, _, value] ->
                             do insideValueConstraints <- gen value
                                xobjType <- toEither (ty xobj) (DefMissingType xobj)
                                valueType <- toEither (ty value) (DefMissingType value)
                                let theTheConstraint = Constraint xobjType valueType xobj value xobj OrdThe
                                return (theTheConstraint : insideValueConstraints)

                           -- Ref
                           [XObj Ref _ _, value] ->
                             gen value

                           -- Deref
                           [XObj Deref _ _, value] ->
                             do insideValueConstraints <- gen value
                                xobjType <- toEither (ty xobj) (ExpressionMissingType xobj)
                                valueType <- toEither (ty value) (ExpressionMissingType value)
                                let lt = VarTy (makeTypeVariableNameFromInfo (info xobj))
                                let theTheConstraint = Constraint (RefTy xobjType lt) valueType xobj value xobj OrdDeref
                                return (theTheConstraint : insideValueConstraints)

                           -- Break
                           [XObj Break _ _] ->
                             return []

                           -- Function application
                           func : args ->
                             do funcConstraints <- gen func
                                variablesConstraints <- fmap join (mapM gen args)
                                funcTy <- toEither (ty func) (ExpressionMissingType func)
                                case funcTy of
                                  (FuncTy argTys retTy _) ->
                                    if length args /= length argTys then
                                      Left (WrongArgCount func (length argTys) (length args))
                                    else
                                      let expected t n =
                                            XObj (Sym (SymPath [] ("Expected " ++ enumerate n ++ " argument to '" ++ getName func ++ "'")) Symbol)
                                            (info func) (Just t)
                                          argConstraints = zipWith4 (\a t aObj n -> Constraint a t aObj (expected t n) xobj OrdFuncAppArg)
                                                                    (List.map forceTy args)
                                                                    argTys
                                                                    args
                                                                    [0..]
                                          Just xobjTy = ty xobj
                                          retConstraint = Constraint xobjTy retTy xobj func xobj OrdFuncAppRet
                                      in  return (retConstraint : funcConstraints ++ argConstraints ++ variablesConstraints)
                                  funcVarTy@(VarTy _) ->
                                    let fabricatedFunctionType = FuncTy (List.map forceTy args) (forceTy xobj) (VarTy "what?!")
                                        expected = XObj (Sym (SymPath [] ("Calling '" ++ getName func ++ "'")) Symbol) (info func) Nothing
                                        wholeTypeConstraint = Constraint funcVarTy fabricatedFunctionType func expected xobj OrdFuncAppVarTy
                                    in  return (wholeTypeConstraint : funcConstraints ++ variablesConstraints)
                                  _ -> Left (NotAFunction func)

                           -- Empty list
                           [] -> Right []

            (Arr arr) ->
              case arr of
                [] -> Right []
                x:xs -> do insideExprConstraints <- fmap join (mapM gen arr)
                           let Just headTy = ty x
                               genObj o n = XObj (Sym (SymPath [] ("Whereas the " ++ enumerate n ++ " element in the array is " ++ show (getPath o))) Symbol)
                                  (info o) (ty o)
                               headObj = XObj (Sym (SymPath [] ("I inferred the type of the array from its first element " ++ show (getPath x))) Symbol)
                                  (info x) (Just headTy)
                               Just (StructTy "Array" [t]) = ty xobj
                               betweenExprConstraints = zipWith (\o n -> Constraint headTy (forceTy o) headObj (genObj o n) xobj OrdArrBetween) xs [1..]
                               headConstraint = Constraint headTy t headObj (genObj x 1) xobj OrdArrHead
                           return (headConstraint : insideExprConstraints ++ betweenExprConstraints)

            -- THIS CODE IS VERY MUCH A DUPLICATION OF THE 'ARR' CODE FROM ABOVE:
            (StaticArr arr) ->
              case arr of
                [] -> Right []
                x:xs -> do insideExprConstraints <- fmap join (mapM gen arr)
                           let Just headTy = ty x
                               genObj o n = XObj (Sym (SymPath [] ("Whereas the " ++ enumerate n ++ " element in the array is " ++ show (getPath o))) Symbol)
                                  (info o) (ty o)
                               headObj = XObj (Sym (SymPath [] ("I inferred the type of the static array from its first element " ++ show (getPath x))) Symbol)
                                  (info x) (Just headTy)
                               Just (RefTy(StructTy "StaticArray" [t]) _) = ty xobj
                               betweenExprConstraints = zipWith (\o n -> Constraint headTy (forceTy o) headObj (genObj o n) xobj OrdArrBetween) xs [1..]
                               headConstraint = Constraint headTy t headObj (genObj x 1) xobj OrdArrHead
                           return (headConstraint : insideExprConstraints ++ betweenExprConstraints)

            _ -> Right []

genConstraintsForCaseMatcher :: MatchMode -> XObj -> Either TypeError [Constraint]
genConstraintsForCaseMatcher matchMode = gen
  where
    -- | NOTE: This works very similar to generating constraints for function calls
    -- | since the cases for sumtypes *are* functions. So we rely on those symbols to
    -- | already have the correct type, e.g. in (match foo (Just x) x) the 'Just' case name
    -- | has the type (Fn [Int] Maybe) which is exactly what we need to give 'x' the correct type.
    gen xobj@(XObj (Lst (caseName : variables)) _ _) =
        do caseNameConstraints <- gen caseName
           variablesConstraints <- fmap join (mapM gen variables)
           caseNameTy <- toEither (ty caseName) (ExpressionMissingType caseName)
           case caseNameTy of
             (FuncTy argTys retTy _) ->
               if length variables /= length argTys then
                 Left (WrongArgCount caseName (length argTys) (length variables)) -- | TODO: This could be another error since this isn't an actual function call.
               else
                 let expected t n = XObj (Sym (SymPath [] ("Expected " ++ enumerate n ++ " argument to '" ++ getName caseName ++ "'")) Symbol) (info caseName) (Just t)
                     argConstraints = zipWith4 (\a t aObj n -> Constraint a t aObj (expected t n) xobj OrdFuncAppArg)
                                               (List.map forceTy variables)
                                               (fmap (wrapInRefTyIfMatchRef matchMode) argTys)
                                               variables
                                               [0..]
                     Just xobjTy = ty xobj
                     retConstraint = Constraint xobjTy retTy xobj caseName xobj OrdFuncAppRet
                 in  return (retConstraint : caseNameConstraints ++ argConstraints ++ variablesConstraints)
             funcVarTy@(VarTy _) ->
               let fabricatedFunctionType = FuncTy (List.map forceTy variables) (forceTy xobj) (VarTy "what?!") -- | TODO: Fix
                   expected = XObj (Sym (SymPath [] ("Matchin on '" ++ getName caseName ++ "'")) Symbol) (info caseName) Nothing
                   wholeTypeConstraint = Constraint funcVarTy fabricatedFunctionType caseName expected xobj OrdFuncAppVarTy
               in  return (wholeTypeConstraint : caseNameConstraints ++ variablesConstraints)
             _ -> Left (NotAFunction caseName) -- | TODO: This error could be more specific too, since it's not an actual function call.
    gen x = return []
