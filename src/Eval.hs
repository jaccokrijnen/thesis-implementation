{-# LANGUAGE PatternSynonyms, FunctionalDependencies, OverloadedLists, FlexibleContexts, GeneralizedNewtypeDeriving, RecursiveDo, OverloadedStrings, LambdaCase, TupleSections, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
module Eval where

import Data.Monoid
import Data.String
import Control.Monad.RWS
import Control.Monad.Identity
import Control.Monad.Except
import Control.Monad.Reader
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Maybe
import Debug.Trace

import Syntax

data MonitorResult
    = MFail String
    | MSuccess
    | MCons MonitorResult MonitorResult
    deriving (Show, Eq)



instance Monoid MonitorResult where    
    m@(MFail _) `mappend` _ = m
    _ `mappend` x = x
    mempty = MSuccess


newtype Eval a =
    Eval {
        runEval ::  ExceptT
                        String
                        (RWS Env MonitorResult ())
                        a
    }
    deriving (Functor, Applicative, Monad, MonadWriter MonitorResult, MonadReader Env, MonadError String, MonadFix)






evalIO :: LambdaPlus -> IO ()
evalIO t = do
    case eval t of
        (Left error, _) -> putStrLn $ "\nLambdaPlus runtime error: \n" <> error
        (_, MFail msg) -> print msg
        (Right v, _) -> print v

eval t =
    let (eValue, (), msg) = (\x -> runRWS x [] ()) . runExceptT . runEval $ eval' t
    in (eValue, msg)



violation :: String -> Eval ()
violation msg = tell (MFail msg)


-- | Basically substitution but without the act of replacing
-- variables, but rememembering the substitution in an environment
-- of the value
addToClosure :: (String, Value) -> Value -> Value
addToClosure (x, xv) = \case
    VCons v1 v2 -> VCons (addToClosure (x, xv) v1) (addToClosure (x, xv) v2)
    VClosure y t env
        | x == y                -> VClosure y t env -- x is shadowed by the closure
        | isJust (lookup x env) -> VClosure y t env -- x is already "bound" by the environment
        | otherwise             -> VClosure y t ((x,xv):env)
    v -> v

unsafeEval :: LambdaPlus -> Value
unsafeEval t =
    case eval t of
        (_,MFail msg) -> error msg
        (Left msg, _) -> error msg
        (Right v, _) -> v

eval' :: LambdaPlus -> Eval Value
eval' t =
    case t of
        LPVar x -> do
            env <- ask
            let prettyEnv = unlines $ map show env
            case lookup x env of
                Nothing -> throwError ("Not in scope: " <> x <> "\nEnvironment: \n" <> prettyEnv <> ")")
                Just v -> return v
        LPApp t1 t2 -> do
            VClosure x t t1Env <- eval' t1
            v <- eval' t2
            let extEnv = (x,v):t1Env
            v' <- local (extEnv ++) (eval' t)
            return $ foldr addToClosure v' extEnv
        LPLet x t1 t2 -> do
            rec v <- local ((x, v):) (eval' t1)
            v' <- local ((x,v):) (eval' t2)
            return (addToClosure (x,v) v')
        LPCons h t ->
            VCons <$> eval' h <*> eval' t
        LPCase t cases -> do
            v <- eval' t
            let matches = mapMaybe (\(p, t) -> (,t) <$> patternMatch p v) cases
            env <- ask
            case matches of
                [] -> throwError $ "No pattern matched for value \n" <> show v <> "\n\n with patterns " <> show (map fst cases) <> "\n\n with env " <> show env
                ((bindings, rhs):_) -> do
                    v'<- local (bindings ++) (eval' rhs)
                    return (foldr addToClosure v' bindings)
        LPVal v -> return v
        LPPlus t1 t2 -> intOp (+) t1 t2
        LPMin t1 t2 -> intOp (-) t1 t2
        LPMul t1 t2 -> intOp (*) t1 t2
        LPAnd t1 t2 -> boolOp (&&) t1 t2
        LPOr t1 t2 -> boolOp (||) t1 t2
        LPGt t1 t2 -> intPred (>) t1 t2
        LPLt t1 t2 -> intPred (<) t1 t2
        LPEq t1 t2 -> (\v1 v2 -> VBool (v1 == v2)) <$> eval' t1 <*> eval' t2
        LPMonitor CTrue t ->
            eval' t
        LPMonitor CFalse t -> do
            violation "False contract occurred"
            eval' t
        LPMonitor (CAnd c1 c2) t -> do
            v <- eval' (LPMonitor c1 t)
            v' <- eval' (LPMonitor c2 t)
            when (v /= v') (throwError "Monitor is inconsistent") -- needed for forcing both evaluations
            return v
        LPMonitor c@(CRefinement x ref describe) t -> do
            v <- eval' t
            res <- local ((x, v):) (evalRefinement ref)
            env <- ((x,v):) <$> ask
            case res of
                VBool True  -> return () >> trace "True" (return ())
                VBool False -> trace "False" (return ()) >> violation (describe (\var -> show . fromJust $ lookup var env))
                _ -> throwError $ "Refinement is not a boolean: " <> show res
            return v
        LPMonitor c@(CDepFunction x c1 c2) t -> do
            VClosure x b env <- eval' t
            return (VClosure x
                       (LPCase (LPMonitor c1 (LPVar x))
                               [(PVar x, (LPMonitor c2 b))]
                       )
                       env
                   )
        _ -> error $ "missed case: " <> show t
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

simplerTerm :: LambdaPlus -> Env -> LambdaPlus
simplerTerm t env = foldr substitute t simpleSubstitutions
    where
        simpleSubstitutions = filter (isSimpleValue . snd) env
        isSimpleValue = \case
            VClosure _ _ _ -> False
            VCons v1 v2 -> isSimpleValue v1 && isSimpleValue v2 
            _ -> True

generateMessage v c = "Value " <> show v <> " does not satisfy " <> show c


evalRefinement :: LambdaPlus -> Eval Value
evalRefinement t = do
    eval' t