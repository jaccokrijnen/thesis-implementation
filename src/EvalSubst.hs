{-# LANGUAGE PatternSynonyms, FunctionalDependencies, OverloadedLists, FlexibleContexts, GeneralizedNewtypeDeriving, RecursiveDo, OverloadedStrings, LambdaCase, TupleSections, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}


-- | This module implements evaluation by performing substitution for variables when
-- bound to a value, as the formal specification states in the thesis.
-- This is however not very efficient in practice, so the actual used implementation
-- can be found in Eval.hs.
module EvalSubst where

import Data.Monoid
import Control.Monad.Writer
import Control.Monad.Except
import Data.Maybe

import Syntax
import Classes



-- | A monad with
--      * exception effect for execution failure (pattern matching, type errors, etc.)
--      * writer effect for collecting the violation messages of contracts
newtype Eval a = Eval (ExceptT
                           String
                           (Writer [MonitorResult])
                           a
                      )
    deriving (Functor, Applicative, Monad, MonadFix, MonadWriter [MonitorResult], MonadError String)


-- | A monitor result
data MonitorResult
    = MFail String
    | MSuccess
    deriving (Show, Eq)


-- | A MonitorResult is a monoid with bias for
-- its left hand side
instance Monoid MonitorResult where
    m@(MFail _) `mappend` _ = m
    _ `mappend` x = x
    mempty = MSuccess


runEval (Eval x) = x


-- | Raise a violation
raiseViolation :: MonitorResult -> Eval ()
raiseViolation m = tell [m]


-- | Evaluate a lambdaplus term
eval :: LambdaPlus -> (Either String Value, [MonitorResult])
eval t = runWriter . runExceptT . runEval $ eval' t


-- | Assume the term always terminates with a value
unsafeEval t = case eval t of
    (Right v, _) -> v


-- | Matches a value with a pattern to produce a series of substitutions (or fail
-- if there exists no unifier)
patternMatch :: Pattern -> Value -> Maybe [(String, Value)]
patternMatch PNil VNil = Just []
patternMatch (PCons p1 p2) (VCons v1 v2) = (++) <$> patternMatch p2 v2 <*> patternMatch p1 v1
patternMatch (PVar x) val = Just [(x, val)]
patternMatch (PBool b1) (VBool b2) | b1 == b2 = Just []
patternMatch _ _ = Nothing



-- | Describes the evaluation semantics in the Eval monad
eval' :: LambdaPlus -> Eval Value
eval' t =
    case t of
        LPVar x ->
            throwError $ "Free variable: " <> x
        LPApp t1 t2 -> do
            VClosure x t _ <- eval' t1
            v        <- eval' t2
            eval' (substitute (x, v) t)
        LPLet x t1 t2 -> do
            v <- eval' (substitute (x, LPLet x t1 (LPVar x)) t1)
            eval' (substitute (x, v) t2)
        LPCons h t ->
            VCons <$> eval' h <*> eval' t
        LPCase t cases -> do
            v <- eval' t
            let matches = mapMaybe (\(p, t) -> (,t) <$> patternMatch p v) cases
            case matches of
                [] -> throwError "No pattern matched"
                ((substitutions, rhs):_) -> eval' (foldr substitute rhs substitutions)
        LPVal v ->
            return v
        LPPlus t1 t2 -> intOp (+) t1 t2
        LPMin t1 t2 -> intOp (-) t1 t2
        LPMul t1 t2 -> intOp (*) t1 t2
        LPAnd t1 t2 -> boolOp (&&) t1 t2
        LPOr t1 t2 -> boolOp (||) t1 t2
        LPGt t1 t2 -> intPred (>) t1 t2
        LPLt t1 t2 -> intPred (<) t1 t2

        LPEq t1 t2 -> do
            v1 <- eval' t1
            v2 <- eval' t2
            return (VBool $ v1 == v2)

        LPMonitor CTrue t ->
            eval' t
        LPMonitor CFalse t -> do
            raiseViolation (MFail "False contract occurred")
            eval' t
        LPMonitor c@(CRefinement var ref describe mbTerm) t -> do
            v <- eval' t
            res <- eval' (substitute (var, v) ref)
            case res of
                (VBool False) -> raiseViolation (MFail $ show t <> " does not satisfy " <> show c)
                (VBool True) -> return ()
                _ -> throwError $ "Type error in contract: " <> show c
            eval' t
        LPMonitor c@(CDepFunction x c1 c2) t -> do
            VClosure x b _ <- eval' t
            return (VClosure x
                       (LPCase (LPMonitor c1 (LPVar x))
                               [(PVar x, (LPMonitor c2 b))]
                       )
                       []
                   )

    where intOp op t1 t2 = do
            (VInt x) <- eval' t1
            (VInt y) <- eval' t2
            return (VInt (x `op` y))
          boolOp op t1 t2 = do
            (VBool x) <- eval' t1
            (VBool y) <- eval' t2
            return (VBool (x `op` y))
          intPred op t1 t2 = do
            (VInt x) <- eval' t1
            (VInt y) <- eval' t2
            return (VBool (x `op` y))
