{-# LANGUAGE PatternSynonyms, FunctionalDependencies, OverloadedLists, FlexibleContexts, GeneralizedNewtypeDeriving, RecursiveDo, OverloadedStrings, LambdaCase, TupleSections, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
module Programs where

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


prelude = def_foldr . def_insert . def_sort


a_foldr :: Annotator
a_foldr c (LPLet x t1 t2) = LPLet x t1 (a_foldr c t2)
a_foldr (CDepFunction _ CTrue c2) (Foldr t1 t2) = Foldr (LPMonitor fContract t1) (LPMonitor eContract t2)
    where
        eContract = c2
        fContract = CTrue `CFunction` CTrue `CFunction` c2
a_foldr c t = a_0 c t


cSorting :: Contract
cSorting = CDepFunction "xs"
                CTrue
                (CRefinement "r" (def_isPerm . def_nonDesc $ apps ["isPerm", "r", "xs"] `LPAnd` app "nonDesc" "r"))

def_isPerm =
    LPLet "isPerm" (lams ["xs", "ys"] (app "sort" "xs" `LPEq` app "sort" "ys"))

def_nonDesc =
    LPLet "nonDesc"
                     (lam "xs"
                        (LPCase "xs"
                            [
                              (PNil, LPVal $ VBool True)
                            , (PCons "x" PNil, LPVal $ VBool True)
                            , (PCons "x" (PCons "y" "xs"), ("x" `LPLt` "y") `LPAnd` (app "nonDesc" (LPCons "y" "xs")))
                            ]
                        )
                     )

ifthenelse :: LambdaPlus -> LambdaPlus -> LambdaPlus -> LambdaPlus
ifthenelse p t1 t2 = LPCase p [(PBool True, t1), (PBool False, t2)]

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

def_sort =
    LPLet "sort"
        (
            lam "xs" (apps ["foldr", "insert", LPVal VNil, "xs"])
        )


{-

CURRENT PROBLEM:

do in ghci:

let f = a_foldr_dep cSorting student_sort
evalIO $ prelude f

??? deF_foldr' moet aan prelude toegevoegd, maar waarom is in het geevalueerde
programma  de term die wordt gemonitord een recursieve call naar foldr?

-}


student_sort = def_insert $ (apps ["foldr", "insert", LPVal VNil])
student_sort_wrong = def_insert_wrong $ (apps ["foldr", "insert", LPVal VNil])

def_insert_wrong =
    (LPLet "insert"
        (
            lams ["x", "xs"]
            (
                LPCase "xs"
                    [
                      (PNil, list ["x"])
                    , (PCons "y" "ys", ifthenelse ("x" `LPLt` "y") (LPCons "x" "ys") (LPCons "y" (apps ["insert", "x", "ys"])) )
                    ]
            )
        )
    )


a_foldr_dep :: Annotator
a_foldr_dep c (LPLet x t1 t2) = LPLet x t1 (a_foldr_dep c t2)
a_foldr_dep (CDepFunction xs CTrue c@(CRefinement _ _)) (Foldr t1 t2) =
    def_foldr' c (apps ["foldr'", t1, t2])
a_foldr_dep c t = a_0 c t

-- Test programs

lams :: [String] -> LambdaPlus -> LambdaPlus
lams vars body = foldr (\var body -> lam var body) body vars

lam v b = LPVal (VClosure v b [])

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

_foldr = def_foldr "foldr"