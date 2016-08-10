{-# LANGUAGE PatternSynonyms, FunctionalDependencies, OverloadedLists, FlexibleContexts, GeneralizedNewtypeDeriving, RecursiveDo, OverloadedStrings, LambdaCase, TupleSections, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
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
        CRefinement x ref -> Set.difference (freeVars ref) [x]
        _ -> []

patternMatch :: Pattern -> Value -> Maybe [(String, Value)]
patternMatch PNil VNil = Just []
patternMatch (PCons p1 p2) (VCons v1 v2) = (++) <$> patternMatch p2 v2 <*> patternMatch p1 v1
patternMatch (PVar x) val = Just [(x, val)]
patternMatch (PBool b1) (VBool b2) | b1 == b2 = Just []
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
                      CRefinement y t
                          | y `elem` introducedVars -> error $ "Captured variable " <> y <> "in refinement contract: " <> show c
                          | y == x -> c
                          | otherwise -> CRefinement y (substitute s t)
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

        LPBinOp op t1 t2 -> (\x y -> x <> " " <> op <> " " <> y) <$> showTerm t1 <*> showTerm t2

        LPMonitor c t -> do
                showT <- showTerm t
                return $ "monitor (" <> show c <> ")" <> "(" <> showT <> ")"

instance Show Contract where
    show = \case
        CTrue -> "True"
        CFalse -> "False"
        CDepFunction "" c1 c2 -> mconcat ["(", show c1, " -> ", show c2, ")"]
        CDepFunction x c1 c2 -> mconcat ["(", x, " : ", show c1, ") ", " -> ", show c2]
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
    | PBool Bool
    deriving (Eq)

instance Show Pattern where
    show (PVar x) = x
    show (PNil) = "[]"
    show (PCons p1 p2) = "(" <> show p1 <> " : " <> show p2 <> ")"
    show (PBool b) = show b

instance IsString Pattern where
    fromString s = PVar s

data Value
    = VInt Int
    | VCons Value Value
    | VNil
    | VLam String LambdaPlus
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
        VLam str term ->
            (\t -> "\\" <> str <> " -> " <> t) <$> showTerm term
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
    | CRefinement String LambdaPlus
    | CDepFunction String Contract Contract
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

unsafeEval t = case eval t of
    (Right v, _) -> v


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
        LPMonitor c@(CRefinement var ref) t -> do
            v <- eval' t
            res <- evalRefinement (substitute (var, v) ref)
            case res of
                (VBool False) -> raiseViolation (MFail $ show t <> " does not satisfy " <> show c)
                (VBool True) -> return ()
                _ -> throwError $ "Type error in contract: " <> show c
            eval' t
        LPMonitor c@(CDepFunction x c1 c2) t -> do
            VLam x b <- eval' t
            return (VLam x
                       (LPCase (LPMonitor c1 (LPVar x))
                               [(PVar x, (LPMonitor c2 b))]
                       )
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

-- Obtain a message somehow
evalRefinement :: LambdaPlus -> Eval Value
evalRefinement t = do
    eval' t


-- * Annotators

type Annotator = Contract -> LambdaPlus -> LambdaPlus

a_0 :: Annotator
a_0 c term = LPMonitor c term


pattern CFunction c1 c2 = CDepFunction "" c1 c2
pattern Foldr t1 t2 = LPApp (LPApp (LPVar "foldr") t1) t2

a_foldr :: Annotator
a_foldr (CDepFunction _ CTrue c2) (Foldr t1 t2) = Foldr (LPMonitor fContract t1) (LPMonitor eContract t2)
    where
        eContract = c2
        fContract = CTrue `CFunction` CTrue `CFunction` c2
a_foldr c t = a_0 c t


cSorted :: Contract
cSorted = undefined

def_isPerm = def_sort .
    LPLet "isPerm" (lams ["xs", "ys"] (app "sort" "xs" `LPEq` app "sort" "ys"))

def_nonDesc =
    LPLet "nondesc"
                     (lam "xs"
                        (LPCase "xs"
                            [
                              (PNil, LPVal $ VBool True)
                            , (PCons "x" PNil, LPVal $ VBool True)
                            , (PCons "x" (PCons "y" "xs"), ("x" `LPLt` "y") `LPAnd` (app "nondesc" (LPCons "y" "xs")))
                            ]
                        )
                     )

ifthenelse :: LambdaPlus -> LambdaPlus -> LambdaPlus -> LambdaPlus
ifthenelse p t1 t2 = LPCase p [(PBool True, t1), (PBool False, t2)]

def_sort = def_foldr .
    LPLet "sort"
                (LPLet "insert"
                    (
                        lams ["x", "xs"]
                        (
                            LPCase "xs"
                                [
                                  (PNil, list ["x"])
                                , (PCons "y" "ys", ifthenelse ("x" `LPLt` "y") (LPCons "x" (LPCons "y" "ys")) (LPCons "y" (apps ["insert", "x", "ys"])) )
                                ]
                        )
                    )
                    (
                        lam "xs" (apps ["foldr", "insert", LPVal VNil, "xs"])
                    )
                )


a_foldr_dep :: Annotator
a_foldr_dep (CDepFunction xs CTrue c@(CRefinement _ _)) (Foldr t1 t2) =
    def_foldr' c (apps ["foldr'", "f", "e"])
a_foldr_dep c t = a_0 c t

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

_sum :: LambdaPlus
_sum = Foldr _plus 0

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

def_foldr' :: Contract -> LambdaPlus -> LambdaPlus
def_foldr' contract = LPLet "foldr'" (lams
                              ["c", "f", "e", "xs"]
                              (LPMonitor contract
                                    (LPCase "xs"
                                        [
                                            (PNil, "e")
                                        ,   (PCons "x" "xs", apps ["f", "x", apps ["foldr'", "c", "f", "e", "xs"]])
                                        ]
                                    )
                              )
                         )

_foldr = def_foldr "foldr"



test_a_0 = a_0 (CRefinement "x" (LPVal (VBool True))) test_foldr


-- * Tests

test_sort = eval $ (def_foldr $ def_sort (app "sort" (list [5,4,3,2,1,3,6])))
test_isPerm = eval $ def_isPerm (apps ["isPerm", list [3,1,4,1,5], list [1,4,3,1,5]])

test_id = eval (app _id _id) == (Right (VLam "x" "x"), [])
test_foldr = def_foldr $ apps ["foldr", _plus, 0, list [1,2,3,4,5]]

test_contract_pass = LPMonitor (CRefinement "x" (LPVal (VBool True))) test_foldr
test_contract_fail = LPMonitor (CRefinement "x" (LPVal (VBool False))) test_foldr

--eval' :: Env -> LambdaPlus -> Value
--eval' env term =
--    case term of
--        LPVar x -> fromMaybe (error "Not in scope: " <> x) (lookup x env)
--        LPApp t1 t2 -> let VLam x t = eval' env t1
--                           arg      = eval' env t2
--                       in eval' ((x, arg):env) t
--        LPLam x t -> VLam x t
--        LPLet x t1 t2 -> let val = eval' env t1 in eval' ((x, val):
