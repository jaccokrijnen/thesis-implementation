{-# LANGUAGE PatternSynonyms, FunctionalDependencies, OverloadedLists, FlexibleContexts, GeneralizedNewtypeDeriving, RecursiveDo, OverloadedStrings, LambdaCase, TupleSections, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
module Tests where

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
import Eval
import Programs


test_a_0 = a_0 (CRefinement "x" (LPVal (VBool True))) test_foldr


-- * Tests

test_sort = eval $ (def_foldr $ def_insert $ def_sort (app "sort" (list [5,4,3,2,1,3,6])))
test_isPerm = eval $ def_isPerm (apps ["isPerm", list [3,1,4,1,5], list [1,4,3,1,5]])

test_id = eval (app _id _id) == (Right (VClosure "x" "x" []), MSuccess)
test_foldr = def_foldr $ apps ["foldr", _plus, 0, list [1,2,3,4,5]]

test_contract_pass = LPMonitor (CRefinement "x" (LPVal (VBool True))) test_foldr
test_contract_fail = LPMonitor (CRefinement "x" (LPVal (VBool False))) test_foldr
