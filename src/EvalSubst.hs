{-# LANGUAGE PatternSynonyms, FunctionalDependencies, OverloadedLists, FlexibleContexts, GeneralizedNewtypeDeriving, RecursiveDo, OverloadedStrings, LambdaCase, TupleSections, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
module EvalSubst where

import Data.Monoid
import Data.String
import Control.Monad.Writer
import Control.Monad.Identity
import Control.Monad.Except
import Control.Monad.Reader
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Maybe

import Syntax






-- This module implements evaluation by performing substitution for variables when 
-- bound to a value, as the formal specification states in the thesis.
-- This is however not very efficient in practice, therefore the actual
-- implementation of operational semantics is in Eval.hs, which uses closures
-- instead.


newtype Eval a = Eval (ExceptT
                           String
                           (Writer [MonitorResult])
                           a
                      )
    deriving (Functor, Applicative, Monad, MonadFix, MonadWriter [MonitorResult], MonadError String)

data MonitorResult
    = MFail String
    | MSuccess
    deriving (Show, Eq)

instance Monoid MonitorResult where
    m@(MFail _) `mappend` _ = m
    _ `mappend` x = x
    mempty = MSuccess


runEval (Eval x) = x

--getVar :: String -> Eval Value
--getVar x = do
--    mbVal <- lookup x <$> ask
--    case mbVal of
--        Nothing -> throwError ("Unbound variable: " <> x)
--        Just v -> return v

raiseViolation :: MonitorResult -> Eval ()
raiseViolation m = tell [m]

eval :: LambdaPlus -> (Either String Value, [MonitorResult])
eval t = runWriter . runExceptT . runEval $ eval' t

unsafeEval t = case eval t of
    (Right v, _) -> v


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
        LPMonitor c@(CRefinement var ref describe) t -> do
            v <- eval' t
            res <- evalRefinement (substitute (var, v) ref)
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

evalRefinement :: LambdaPlus -> Eval Value
evalRefinement t = do
    eval' t
