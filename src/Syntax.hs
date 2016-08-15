{-# LANGUAGE PatternSynonyms, FunctionalDependencies, OverloadedLists, FlexibleContexts, GeneralizedNewtypeDeriving, RecursiveDo, OverloadedStrings, LambdaCase, TupleSections, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}
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

    | LPBinOp String LambdaPlus LambdaPlus

    | LPMonitor Contract LambdaPlus
    deriving (Eq)

pattern LPPlus c1 c2 = LPBinOp "+" c1 c2
pattern LPMin c1 c2 = LPBinOp "-" c1 c2
pattern LPMul c1 c2 = LPBinOp "*" c1 c2
pattern LPDiv c1 c2 = LPBinOp "/" c1 c2
pattern LPAnd c1 c2 = LPBinOp "&&" c1 c2
pattern LPOr c1 c2 = LPBinOp "||" c1 c2
pattern LPEq c1 c2 = LPBinOp "==" c1 c2
pattern LPLt c1 c2 = LPBinOp "<" c1 c2
pattern LPGt c1 c2 = LPBinOp ">" c1 c2




instance IsString LambdaPlus where
    fromString s = LPVar s

instance Num LambdaPlus where
    fromInteger n = LPVal (VInt (fromIntegral n))
    (+) = LPPlus
    (*) = LPMul
    (-) = LPMin

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
        LPBinOp op t1 t2 -> freeVars t1 <> freeVars t2


instance HasVars Contract String where
    freeVars = \case
        CDepFunction x c1 c2 -> Set.difference (freeVars c1 <> freeVars c2) [x]
        CRefinement x ref _ -> Set.difference (freeVars ref) [x]
        CAnd c1 c2 -> (freeVars c1) <> (freeVars c2)
        _ -> []

patternMatch :: Pattern -> Value -> Maybe [(String, Value)]
patternMatch PNil VNil = Just []
patternMatch (PCons p1 p2) (VCons v1 v2) = (++) <$> patternMatch p2 v2 <*> patternMatch p1 v1
patternMatch (PVar x) val = Just [(x, val)]
patternMatch (PBool b1) (VBool b2) | b1 == b2 = Just []
patternMatch _ _ = Nothing

instance HasVars Value String where
    freeVars = \case
        VClosure x t _ -> freeVars t `Set.difference` [x]
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
                    (LPBinOp op t1 t2) ->
                        LPBinOp op (substitute' t1) (substitute' t2)
                    (LPMonitor c t) ->
                        LPMonitor (substitute s c) (substitute' t)

instance Substitutable LambdaPlus Value String where
    substitute (x, v) = substitute (x, LPVal v)

instance Substitutable Contract LambdaPlus String where
    substitute s@(x, t) = substitute'
        where introducedVars = freeVars t
              substitute' c =
                  case c of
                      CDepFunction y c1 c2
                          | y `elem` introducedVars -> error $ "Captured variable " <> y <> "in function contract: " <> show c
                          | y == x -> c
                          | otherwise -> CDepFunction y (substitute' c1) (substitute' c2)
                      CRefinement y t descr
                          | y `elem` introducedVars -> error $ "Captured variable " <> y <> "in refinement contract: " <> show c
                          | y == x -> c
                          | otherwise -> CRefinement y (substitute s t) descr
                      c -> c

binds :: Pattern -> String -> Bool
binds p x = x `elem` (boundVars p)

boundVars :: Pattern -> Set String
boundVars (PCons p1 p2) = boundVars p1 <> boundVars p2
boundVars (PVar x) = [x]
boundVars _ = []

instance Substitutable Value LambdaPlus String where
    substitute s@(x, t) v = substitute' v
        where
              introducedVars = freeVars t
              substitute' v =
                case v of
                    VCons v1 v2 -> VCons (substitute' v1) (substitute' v2)
                    VClosure y t1 env
                        | y `elem` introducedVars -> error $ "Captured variable " <> y <> "in lambda: " <> show v
                        | x == y -> VClosure y t1 env
                        | otherwise -> VClosure y (substitute s t1) env
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
                    <*> local (+indentAmount) (showTerm t2)
        LPCase t cases ->
            (\x ys -> "case " <> x <> " of " <> "\n" <> ys)
                <$> showTerm t
                <*> local (+indentAmount) (showCases cases)
        LPCons t1 t2 -> (\x y -> x <> " : " <> y) <$> showTerm t1 <*> showTerm t2
        LPVal v -> showValue v

        LPBinOp op t1 t2 -> (\x y -> x <> " " <> op <> " " <> y) <$> showTerm t1 <*> showTerm t2

        LPMonitor c t -> do
                showT <- local (+indentAmount) (showTerm t)
                return $ "monitor (" <> show c <> ")" <> "\n" <> whitespace depth <> "(" <> showT <> ")"

instance Show Contract where
    show = \case
        CTrue -> "True"
        CFalse -> "False"
        CAnd c1 c2 -> show c1 <> " AND " <> show c2
        CDepFunction "" c1 c2 -> mconcat ["(", show c1, " -> ", show c2, ")"]
        CDepFunction x c1 c2 -> mconcat ["(", x, " : ", show c1, ") ", " -> ", show c2]
        CRefinement x t describe -> mconcat ["{", x, " : ", describe id, "}" ]

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
    | PBool Bool
    deriving (Eq)

instance Show Pattern where
    show (PVar x) = x
    show (PNil) = "[]"
    show (PCons p1 p2) = "(" <> show p1 <> " : " <> show p2 <> ")"
    show (PBool b) = show b

instance IsString Pattern where
    fromString s = PVar s

type Env = [(String, Value)]

data Value
    = VInt Int
    | VCons Value Value
    | VNil
    | VClosure String LambdaPlus Env
    | VBool Bool
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
        VClosure str term env ->
            let prettyEnv = if null env then "" else "ENV: " <> show env <> ")"
            in  (\t -> "\\" <> str <> " -> " <> t <> prettyEnv) <$> showTerm term
        (VBool True) -> return "True"
        (VBool False) -> return "False"
-- TODO alpha equivalence

--instance Eq Value where
--    (VInt x)    == (VInt y)    = x == y
--    (VCons x y) == (VCons z w) = x == y && z == w
--    VNil == VNil = True
--    (VLam v)

data Contract
    = CTrue
    | CFalse
    | CAnd Contract Contract
    | CRefinement String -- variable referring to current value
                  LambdaPlus -- Boolean valued term
                  ((String -> String) -> String)  -- description of this refinement for feedback message, passed a function to describe variables (e.g. an environment lookup)
    | CDepFunction String Contract Contract
    deriving Eq

instance Eq ((String -> String)-> String) where
    _ == _ = True

--contractMessage :: Env -> Contract -> String
--contractMessage env c = \case ->
--    CTrue  -> "True"
--    CFalse -> "False"
--contractMessage (CRefinement _ _ description) = description
--contractMessage (CAnd c1 c2) = contractMessage c1 <> " and " <> contractMessage c2
--contractMessage (CDepFunction x c1 c2) = contractMessage c1 <> " on its domain " <> x <>  ", and " <> contractMessage c2 <> " on its result" 
-- * evaluation



-- * Evaluation with an environment instead of substitutions







-- * Annotators


list :: [LambdaPlus] -> LambdaPlus
list = foldr LPCons (LPVal VNil)


type Annotator = Contract -> LambdaPlus -> LambdaPlus

a_0 :: Annotator
a_0 c term = LPMonitor c term


pattern CFunction c1 c2 = CDepFunction "" c1 c2
