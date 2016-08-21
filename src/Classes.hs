{-# LANGUAGE FunctionalDependencies, FlexibleContexts, MultiParamTypeClasses #-}
module Classes where

import Data.Set

-- | A class to collect free variables in some term
class HasVars term var | term -> var where
    freeVars :: term -> Set var


-- | A class to substitute a term inside another term
class Substitutable term insertTerm var | term -> var where
    substitute :: (var, insertTerm) -> term -> term