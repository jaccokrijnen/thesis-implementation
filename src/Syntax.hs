{-# LANGUAGE FunctionalDependencies, OverloadedLists, FlexibleContexts, GeneralizedNewtypeDeriving, RecursiveDo, OverloadedStrings, LambdaCase, TupleSections, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
module Syntax where

import Data.Monoid
import Data.String
import Control.Monad.Writer
import Control.Monad.Identity
import Control.Monad.Except
import Control.Monad.Reader
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Maybe

data LambdaPlus
    = LPVar String
    | LPApp LambdaPlus LambdaPlus
    | LPLet String LambdaPlus LambdaPlus
    | LPCase LambdaPlus [(Pattern, LambdaPlus)]

    | LPCons LambdaPlus LambdaPlus
    | LPVal Value

    | LPPlus LambdaPlus LambdaPlus

    | LPMonitor Contract LambdaPlus
    deriving (Eq)

instance IsString LambdaPlus where
    fromString s = LPVar s

instance Num LambdaPlus where
    fromInteger n = LPVal (VInt (fromIntegral n))

instance Show LambdaPlus where
    show t = runReader (showTerm t) 0

class HasVars term var | term -> var where
    freeVars :: term -> Set var

instance HasVars LambdaPlus String where
    freeVars = \case
        LPVar x -> [x]
        LPApp t1 t2 -> freeVars t1 <> freeVars t2
        LPLet x t1 t2 -> Set.difference (freeVars t1 <> freeVars t2) [x]
        LPCase t cases ->
            let freeVarsCase (p, t1) = freeVars t1 `Set.difference` boundVars p
            in freeVars t <> Set.unions (map freeVarsCase cases)
        LPCons t1 t2 -> freeVars t1 <> freeVars t2
        LPVal v -> freeVars v
        LPPlus t1 t2 -> freeVars t1 <> freeVars t2
        LPMonitor c t -> freeVars c <> freeVars t

instance HasVars Contract String where
    freeVars = \case
        CFunction x c1 c2 -> Set.difference (freeVars c1 <> freeVars c2) [x]
        CRefinement x ref -> Set.difference (freeVars ref) [x]
        _ -> []

patternMatch :: Pattern -> Value -> Maybe [(String, Value)]
patternMatch PNil VNil = Just []
patternMatch (PCons p1 p2) (VCons v1 v2) = patternMatch p1 v1 <> patternMatch p2 v2
patternMatch (PVar x) term = Just [(x, term)]
patternMatch _ _ = Nothing

instance HasVars Value String where
    freeVars = \case
        VLam x t -> freeVars t `Set.difference` [x]
        VCons v1 v2 -> freeVars v1 <> freeVars v2
        _ -> []

class Substitutable term insertTerm var | term -> var where
    substitute :: (var, insertTerm) -> term -> term

instance Substitutable LambdaPlus LambdaPlus String where
    substitute s@(x, xt) t = substitute' t

        where introducedVars = freeVars xt
              substitute' t =
                case t of
                    (LPVar y)
                        | y == x -> xt
                        | otherwise -> LPVar y
                    (LPApp t1 t2) -> LPApp (substitute' t1) (substitute' t2)
                    (LPLet y t1 t2)
                        | y `elem` introducedVars -> error $ "Captured variable " <> y <> "in let: " <> show t
                        | y == x -> t
                        | otherwise -> LPLet y (substitute' t1) (substitute' t2)
                    (LPCase t cases) ->
                        let substCase (p, t1)
                                | Set.intersection (boundVars p) introducedVars /= [] = error $ "Captured variables " <> show (Set.intersection (boundVars p) introducedVars) <> " in case: " <> show t1
                                | binds p x = (p, t1)
                                | otherwise = (p, substitute' t1)
                        in LPCase (substitute' t) (map substCase cases)
                    (LPCons t1 t2) ->
                        LPCons (substitute' t1) (substitute' t2)
                    (LPVal v) ->
                        LPVal (substitute s v)
                    (LPPlus t1 t2) ->
                        LPPlus (substitute' t1) (substitute' t2)
                    (LPMonitor c t) ->
                        LPMonitor (substitute s c) (substitute' t)

instance Substitutable LambdaPlus Value String where
    substitute (x, v) = substitute (x, LPVal v)

instance Substitutable Contract LambdaPlus String where
    substitute s@(x, t) = substitute'
        where introducedVars = freeVars t
              substitute' c =
                  case c of
                      CFunction y c1 c2
                          | y `elem` introducedVars -> error $ "Captured variable " <> y <> "in function contract: " <> show c
                          | y == x -> c
                          | otherwise -> CFunction y (substitute' c1) (substitute' c2)
                      CRefinement y t
                          | y `elem` introducedVars -> error $ "Captured variable " <> y <> "in refinement contract: " <> show c
                          | y == x -> c
                          | otherwise -> CRefinement y (substitute s t)
                      c -> c

binds :: Pattern -> String -> Bool
binds p x = x `elem` (boundVars p)

boundVars :: Pattern -> Set String
boundVars PNil = []
boundVars (PCons p1 p2) = boundVars p1 <> boundVars p2
boundVars (PVar x) = [x]

instance Substitutable Value LambdaPlus String where
    substitute s@(x, t) v = substitute' v
        where
              introducedVars = freeVars t
              substitute' v =
                case v of
                    VCons v1 v2 -> VCons (substitute' v1) (substitute' v2)
                    VLam y t1
                        | y `elem` introducedVars -> error $ "Captured variable " <> y <> "in lambda: " <> show v
                        | x == y -> VLam y t1
                        | otherwise -> VLam y (substitute s t1)
                    _ -> v

instance Substitutable Value Value String where
    substitute (x, v) = substitute (x, LPVal v)

type Indentation = Int

indentAmount = 4

whitespace n = replicate n ' '

showTerm :: LambdaPlus -> Reader Indentation String
showTerm term = do
    depth <- ask
    case term of
        LPVar v -> return v
        LPApp t1 t2 ->
            (\x y -> "(" <> x <> " " <> y <> ")")
                <$> showTerm t1
                <*> showTerm t2
        LPLet v t1 t2 ->
            (\x y -> "let " <> v <> " = " <> x <> "\n" <> whitespace depth <> ("in " <> y))
                    <$> showTerm t1
                    <*> showTerm t2
        LPCase t cases ->
            (\x ys -> "case " <> x <> " of " <> "\n" <> ys)
                <$> showTerm t
                <*> local (+indentAmount) (showCases cases)
        LPCons t1 t2 -> (\x y -> x <> " : " <> y) <$> showTerm t1 <*> showTerm t2
        LPVal v -> showValue v

        LPPlus t1 t2 -> (\x y -> x <> " + " <> y) <$> showTerm t1 <*> showTerm t2

        LPMonitor c t -> do
                showT <- showTerm t
                return $ "monitor (" <> show c <> ")" <> "(" <> showT <> ")"

instance Show Contract where
    show = \case
        CTrue -> "True"
        CFalse -> "False"
        CFunction x c1 c2 -> mconcat ["(", x, " : ", show c1, ") ", " -> ", show c2]
        CRefinement x t -> mconcat ["{", x, " : ", show t, "}" ]

showCases :: [(Pattern, LambdaPlus)] -> Reader Indentation String
showCases cs = unlines <$> mapM showCase cs
    where showCase (p, term) =
              (\n t -> whitespace n <> show p <> " -> " <> t)
                    <$> ask
                    <*> showTerm term

data Pattern
    = PVar String
    | PNil
    | PCons Pattern Pattern
    deriving (Eq)

instance Show Pattern where
    show (PVar x) = x
    show (PNil) = "[]"
    show (PCons p1 p2) = "(" <> show p1 <> " : " <> show p2 <> ")"

instance IsString Pattern where
    fromString s = PVar s

data Value
    = VInt Int
    | VCons Value Value
    | VNil
    | VLam String LambdaPlus
    | VTrue
    | VFalse
    deriving (Eq)

instance Show Value where
    show v = runReader (showValue v) 0

showValue :: Value -> Reader Indentation String
showValue v = do
    case v of
        VInt x ->
            return (show x)
        VCons v1 v2 ->
            (\x y -> x <> " : " <> y)
                <$> (showValue v1)
                <*> (showValue v2)
        VNil -> return "[]"
        VLam str term ->
            (\t -> "\\" <> str <> " -> " <> t) <$> showTerm term
        VTrue -> return "True"
        VFalse -> return "False"
-- TODO alpha equivalence

--instance Eq Value where
--    (VInt x)    == (VInt y)    = x == y
--    (VCons x y) == (VCons z w) = x == y && z == w
--    VNil == VNil = True
--    (VLam v)

data Contract
    = CTrue
    | CFalse
    | CRefinement String LambdaPlus
    | CFunction String Contract Contract
    deriving (Eq)

-- * evaluation

type Env = [(String, Value)]

data MonitorResult
    = MFail String
    | MSuccess
    deriving (Show, Eq)

instance Monoid MonitorResult where
    m@(MFail _) `mappend` _ = m
    _ `mappend` x = x
    mempty = MSuccess

newtype Eval a = Eval (ExceptT
                           String
                           (Writer [MonitorResult])
                           a
                      )
    deriving (Functor, Applicative, Monad, MonadFix, MonadWriter [MonitorResult], MonadError String)

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

eval' :: LambdaPlus -> Eval Value
eval' t =
    case t of
        LPVar x ->
            throwError $ "Free variable: " <> x
        LPApp t1 t2 -> do
            VLam x t <- eval' t1
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
        LPPlus t1 t2 -> do
            (VInt x) <- eval' t1
            (VInt y) <- eval' t2
            return (VInt (x+y))
        LPMonitor CTrue t ->
            eval' t
        LPMonitor CFalse t -> do
            raiseViolation (MFail "False contract occurred")
            eval' t
        LPMonitor c@(CRefinement var ref) t -> do
            v <- eval' t
            res <- evalRefinement (substitute (var, v) ref)
            case res of
                VFalse -> raiseViolation (MFail $ show t <> " does not satisfy " <> show c)
                VTrue -> return ()
                _ -> throwError $ "Type error in contract: " <> show c
            eval' t
        LPMonitor c@(CFunction x c1 c2) t -> do
            VLam x b <- eval' t
            return (VLam x
                       (LPCase (LPMonitor c1 (LPVar x))
                               [(PVar x, (LPMonitor c2 b))]
                       )
                   )

-- Obtain a message somehow
evalRefinement :: LambdaPlus -> Eval Value
evalRefinement t = do
    eval' t


-- Test programs

lams :: [String] -> LambdaPlus -> LambdaPlus
lams vars body = foldr (\var body -> LPVal (VLam var body)) body vars

lam v b = LPVal (VLam v b)

app = LPApp

apps :: [LambdaPlus] -> LambdaPlus
apps terms = foldl1 LPApp terms

cons :: LambdaPlus
cons = lams ["x", "xs"] (LPCons "x" "xs")

nil = LPVal VNil

_id :: LambdaPlus
_id = lam "x" "x"

_const :: LambdaPlus
_const = lams ["x","y"] "x"

list :: [LambdaPlus] -> LambdaPlus
list = foldr LPCons (LPVal VNil)

_plus = lams ["x", "y"] (LPPlus "x" "y")

def_foldr :: LambdaPlus -> LambdaPlus
def_foldr = LPLet "foldr" (lams
                              ["f", "e", "xs"]
                              (LPCase "xs"
                                    [
                                        (PNil, "e")
                                    ,   (PCons "x" "xs", apps ["f", "x", apps ["foldr", "f", "e", "xs"]])
                                    ]
                              )
                         )

_foldr = def_foldr "foldr"



-- * Tests

test_id = eval (app _id _id) == (Right (VLam "x" "x"), [])
test_foldr = def_foldr $ apps ["foldr", _plus, 0, list [1,2,3,4,5]]

test_contract_pass = LPMonitor (CRefinement "x" (LPVal VTrue)) test_foldr
test_contract_fail = LPMonitor (CRefinement "x" (LPVal VFalse)) test_foldr

--eval' :: Env -> LambdaPlus -> Value
--eval' env term =
--    case term of
--        LPVar x -> fromMaybe (error "Not in scope: " <> x) (lookup x env)
--        LPApp t1 t2 -> let VLam x t = eval' env t1
--                           arg      = eval' env t2
--                       in eval' ((x, arg):env) t
--        LPLam x t -> VLam x t
--        LPLet x t1 t2 -> let val = eval' env t1 in eval' ((x, val):
