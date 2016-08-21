{-# LANGUAGE PatternSynonyms, FunctionalDependencies, OverloadedLists, FlexibleContexts, GeneralizedNewtypeDeriving, RecursiveDo, OverloadedStrings, LambdaCase, TupleSections, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

-- | This module introduces the syntax of LambdaPlus and contracts
-- with the nessecary utility functions/class instances
module Syntax where

import Data.Monoid
import Data.String
import Control.Monad.Reader
import qualified Data.Set as Set
import Data.Set (Set)
import Classes


-- | A Lambdaplus term
data LambdaPlus
    = LPVar String
    | LPApp LambdaPlus LambdaPlus
    | LPLet String LambdaPlus LambdaPlus
    | LPCase LambdaPlus [(Pattern, LambdaPlus)]

    | LPCons LambdaPlus LambdaPlus
    | LPVal Value

    | LPBinOp String LambdaPlus LambdaPlus

    | LPMonitor Contract LambdaPlus

    | LPTransformedTo LambdaPlus LambdaPlus
    deriving (Eq)


-- | Convenient patterns/constructors for LambdaPlus operators
pattern LPPlus c1 c2 = LPBinOp "+" c1 c2
pattern LPMin c1 c2  = LPBinOp "-" c1 c2
pattern LPMul c1 c2  = LPBinOp "*" c1 c2
pattern LPDiv c1 c2  = LPBinOp "/" c1 c2
pattern LPAnd c1 c2  = LPBinOp "&&" c1 c2
pattern LPOr c1 c2   = LPBinOp "||" c1 c2
pattern LPEq c1 c2   = LPBinOp "==" c1 c2
pattern LPLt c1 c2   = LPBinOp "<" c1 c2
pattern LPGt c1 c2   = LPBinOp ">" c1 c2


-- | A Lambdaplus pattern
data Pattern
    = PVar String
    | PNil
    | PCons Pattern Pattern
    | PBool Bool
    deriving (Eq)


-- | An environment used for representing closures and used during evaluation
type Env = [(String, Value)]


-- | Values
data Value
    = VInt Int
    | VCons Value Value
    | VNil
    | VClosure String LambdaPlus Env
    | VBool Bool
    deriving (Eq)


-- | Representation of a contract
data Contract
    = CTrue
    | CFalse
    | CAnd Contract Contract
    | CRefinement
          String                           -- ^ Variable referring to current value
          LambdaPlus                       -- ^ The refinement, a boolean valued term that can use variables in scope
          ((String -> String) -> String)   -- ^ Description of this refinement for pretty printing a contract, also used for feedback message
          (Maybe (Env -> LambdaPlus))      -- ^ A term to display in the error message instead of the computed value that breaks the contract,
                                           -- ^ should be an intermediate term during evaluation (for instance the student program + input).
                                           -- ^ If none is provided the evaluated value will be reported
    | CDepFunction String Contract Contract
    deriving Eq

pattern CFunction c1 c2 = CDepFunction "" c1 c2


type Annotator = Contract -> LambdaPlus -> LambdaPlus


----------------------------------------------------------
-- * Instances for LambdaPlus terms
----------------------------------------------------------


instance IsString LambdaPlus where
    fromString s = LPVar s

instance Num LambdaPlus where
    fromInteger n = LPVal (VInt (fromIntegral n))
    (+) = LPPlus
    (*) = LPMul
    (-) = LPMin
    abs = undefined
    signum = undefined

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
        t1 `LPTransformedTo` t2 -> freeVars t2


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
                    (LPTransformedTo t1 t2) ->
                        LPTransformedTo t1 (substitute' t2)

instance Substitutable LambdaPlus Value String where
    substitute (x, v) = substitute (x, LPVal v)


instance Show LambdaPlus where
    show t = runReader (showTerm t) 0

type Indentation = Int

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
        LPTransformedTo t1 t2 -> showTerm t2


indentAmount = 4

whitespace n = replicate n ' '


showCases :: [(Pattern, LambdaPlus)] -> Reader Indentation String
showCases cs = unlines <$> mapM showCase cs
    where showCase (p, term) =
              (\n t -> whitespace n <> show p <> " -> " <> t)
                    <$> ask
                    <*> showTerm term


-- | Fake instances needed for deriving Eq on terms (this is not a problem since contract
-- descriptions are used when a violation is raised and do not influence the semantics
instance Eq ((String -> String)-> String) where
    _ == _ = True

instance Eq (Env -> LambdaPlus) where
    _ == _ = True

----------------------------------------------------------
-- * Instances for values
----------------------------------------------------------


instance HasVars Value String where
    freeVars = \case
        VClosure x t _ -> freeVars t `Set.difference` [x]
        VCons v1 v2 -> freeVars v1 <> freeVars v2
        _ -> []



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


instance Show Value where
    show v = runReader (showValue v) 0

showValue :: Value -> Reader Indentation String
showValue v | Just vs <- toList v =
    return (show vs)
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

toList :: Value -> Maybe [Value]
toList (VCons x t) = (x:) <$> toList t
toList VNil = Just []
toList _ = Nothing


----------------------------------------------------------
-- * Instances for contracts
----------------------------------------------------------

instance HasVars Contract String where
    freeVars = \case
        CDepFunction x c1 c2 -> Set.difference (freeVars c1 <> freeVars c2) [x]
        CRefinement x ref _ _ -> Set.difference (freeVars ref) [x]
        CAnd c1 c2 -> (freeVars c1) <> (freeVars c2)
        _ -> []


instance Substitutable Contract LambdaPlus String where
    substitute s@(x, t) = substitute'
        where introducedVars = freeVars t
              substitute' c =
                  case c of
                      CDepFunction y c1 c2
                          | y `elem` introducedVars -> error $ "Captured variable " <> y <> "in function contract: " <> show c
                          | y == x -> c
                          | otherwise -> CDepFunction y (substitute' c1) (substitute' c2)
                      CRefinement y t describe mTerm
                          | y `elem` introducedVars -> error $ "Captured variable " <> y <> "in refinement contract: " <> show c
                          | y == x -> c
                          | otherwise -> CRefinement y (substitute s t) describe mTerm
                      c -> c


instance Show Contract where
    show = \case
        CTrue -> "True"
        CFalse -> "False"
        CAnd c1 c2 -> show c1 <> " AND " <> show c2
        CDepFunction "" c1 c2 -> mconcat ["(", show c1, " -> ", show c2, ")"]
        CDepFunction x c1 c2 -> mconcat ["(", x, " : ", show c1, ") ", " -> ", show c2]
        CRefinement x t describe _ -> mconcat ["{", x, " : ", describe id, "}" ]




----------------------------------------------------------
-- * Instances for patterns
----------------------------------------------------------


instance Show Pattern where
    show (PVar x) = x
    show (PNil) = "[]"
    show (PCons p1 p2) = "(" <> show p1 <> " : " <> show p2 <> ")"
    show (PBool b) = show b

instance IsString Pattern where
    fromString s = PVar s


----------------------------------------------------------
-- * General utility functions
----------------------------------------------------------


binds :: Pattern -> String -> Bool
binds p x = x `elem` (boundVars p)


boundVars :: Pattern -> Set String
boundVars (PCons p1 p2) = boundVars p1 <> boundVars p2
boundVars (PVar x) = [x]
boundVars _ = []


list :: [LambdaPlus] -> LambdaPlus
list = foldr LPCons (LPVal VNil)


lams :: [String] -> LambdaPlus -> LambdaPlus
lams vars body = foldr (\var body -> lam var body) body vars

lam v b = LPVal (VClosure v b [])

app = LPApp

apps :: [LambdaPlus] -> LambdaPlus
apps terms = foldl1 LPApp terms


dropLets :: LambdaPlus -> LambdaPlus
dropLets (LPLet _ _ t) = dropLets t
dropLets t = t







