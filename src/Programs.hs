{-# LANGUAGE PatternSynonyms, FunctionalDependencies, OverloadedLists, FlexibleContexts, GeneralizedNewtypeDeriving, RecursiveDo, OverloadedStrings, LambdaCase, TupleSections, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}

-- | This module introduces programs in LambdaPlus,
-- some annotators and contracts
module Programs where

import Data.Monoid

import Syntax

----------------------------------------------------------
-- * Annotators
----------------------------------------------------------


-- | The trivial annotator
a_0 :: Annotator
a_0 c term = LPMonitor c term


-- | A consistent anntoator for foldr, which cannot handle dependent contracts
a_foldr :: Annotator
a_foldr c (LPLet x t1 t2) = LPLet x t1 (a_foldr c t2)
a_foldr (CDepFunction _ CTrue c2) (Foldr t1 t2) = Foldr (LPMonitor fContract t1) (LPMonitor eContract t2)
    where
        eContract = c2
        fContract = CTrue `CFunction` CTrue `CFunction` c2
a_foldr c t = a_0 c t


-- | Pattern/constructor for a term of the form "foldr t1 t2"
pattern Foldr t1 t2 = LPApp (LPApp (LPVar "foldr") t1) t2


-- | A consistent annotator for programs described as a foldr which handles dependent contracts
a_foldr_dep :: Annotator
a_foldr_dep c (LPLet x t1 t2) = LPLet x t1 (a_foldr_dep c t2)
a_foldr_dep (CDepFunction xs CTrue c) (Foldr t1 t2) =
    def_foldr' (t1, t2) c $ (apps ["foldr'", t1, t2])
a_foldr_dep c t = a_0 c t


----------------------------------------------------------
-- * Contracts
----------------------------------------------------------


-- | A contract which states the sorting specificion:
-- non-descending and a permutation of the input
cSorting :: Contract
cSorting = cSorting' Nothing


-- | A contract which states the sorting specificion:
-- non-descending and a permutation of the input
-- The optional argument is a term that is used for
-- displaying the original program in the violation message.
cSorting' :: Maybe (Env -> LambdaPlus) -> Contract
cSorting' mEnv2term =
    CDepFunction "xs"
        CTrue
        (CAnd (CRefinement
                  "r"
                  (def_nonDesc $ app "nonDesc" "r")
                  (const "non-descending")
                  mEnv2term
              )
              (CRefinement
                  "r"
                  (def_sort . def_isPerm $ apps ["isPerm", "r", "xs"])
                  (\var2str -> "a permutation of " <> var2str "xs")
                  mEnv2term
              )
        )

----------------------------------------------------------
-- * Programs in LambdaPlus
--
-- Reusable definitions are prefixed with def_ and have type LambdaPlus -> LambdaPlus, as they
-- introduce a let-bound variable that can be referenced as variable in LambdaPlus terms.
----------------------------------------------------------



-- | Collection of useful definitions, use it like:
-- >>> evalIO . prelude $ myTerm
prelude = def_foldr . def_insert . def_sort


-- | if-then-else is translated to a boolean
ifthenelse :: LambdaPlus -> LambdaPlus -> LambdaPlus -> LambdaPlus
ifthenelse p t1 t2 = LPCase p [(PBool True, t1), (PBool False, t2)]


-- | Identity function
_id :: LambdaPlus
_id = lam "x" "x"


-- | Constant function
_const :: LambdaPlus
_const = lams ["x","y"] "x"


-- | Sum of a list of integers
_sum :: LambdaPlus
_sum = Foldr _plus 0


-- | Curried plus operator
_plus = lams ["x", "y"] (LPPlus "x" "y")


-- | Definition of foldr
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


-- | Identity function
def_id = LPLet "id" (lam "x" "x")


-- | Cons
cons :: LambdaPlus
cons = lams ["x", "xs"] (LPCons "x" "xs")


-- | Nil
nil = LPVal VNil

-- | The correct insert function which inserts an integer
-- in a sorted list of integers on the correct place
def_insert :: LambdaPlus -> LambdaPlus
def_insert =
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
    )


-- | Insertion sort on list of integers
def_sort :: LambdaPlus -> LambdaPlus
def_sort =
    LPLet "sort"
        (
            lam "xs" (apps ["foldr", "insert", LPVal VNil, "xs"])
        )


-- | Predicate that checks if two lists are permutations
def_isPerm =
    LPLet "isPerm" (lams ["xs", "ys"] (app "sort" "xs" `LPEq` app "sort" "ys"))


-- | Predicate that checks if a list of integers is non-descending
def_nonDesc =
    LPLet "nonDesc"
                     (lam "xs"
                        (LPCase "xs"
                            [
                              (PNil, LPVal $ VBool True)
                            , (PCons "x" PNil, LPVal $ VBool True)
                            , (PCons "x" (PCons "y" "xs"), (("x" `LPLt` "y") `LPOr` ("x" `LPEq` "y")) `LPAnd` (app "nonDesc" (LPCons "y" "xs")))
                            ]
                        )
                     )


-- | Student programs for attempts to implement insertion sort
student_sort               = def_insert       $ apps ["foldr", "insert", LPVal VNil]
student_sort_wrong_perm    = def_insert_wrong $ apps ["foldr", "insert_wrong", LPVal VNil]
student_sort_wrong_nondesc = def_id           $ apps ["foldr", cons, LPVal VNil]


-- | Incorrect insert function which forgets to include variable y in the first
-- case of the if-then-else
def_insert_wrong =
    (LPLet "insert_wrong"
        (
            lams ["x", "xs"]
            (
                LPCase "xs"
                    [
                      (PNil          , list ["x"])
                    , (PCons "y" "ys", ifthenelse ("x" `LPLt` "y")
                                           (LPCons "x" "ys")
                                           (LPCons "y" (apps ["insert", "x", "ys"])) )
                    ]
            )
        )
    )




-- | Used by a_foldr_dep. Introduces a definition onf foldr' with specific feedback using
-- the terms of the arguments of foldr for better feedback messages
def_foldr' :: (LambdaPlus, LambdaPlus) -> Contract -> LambdaPlus -> LambdaPlus
def_foldr' (f, e) contract =
    LPLet "foldr'" (lams
                        ["f", "e", "xs"]
                        (LPMonitor contract
                              (LPCase "xs"
                                  [
                                      (PNil, "e")
                                  ,   (PCons "x" "xs", apps ["f", "x", apps ["foldr'", "f", "e", "xs"]])
                                  ]
                              )
                        )
                   )


-- | Foldr in curried form
_foldr = def_foldr "foldr"