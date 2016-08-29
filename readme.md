Master thesis implementation (Better Feedback for Incorrect Programs by Using Contracts)
====

This package is a prototype of the lambda-plus language and annotators as described in my master thesis. All modules are self-documented. To see the result of the annotators, run:

```
$ cabal sandbox init
$ cabal install
$ cabal repl
$ import Demo
$ sort_correct
$ sort_incorrect_perm
$ sort_incorrect_nondesc
```

For student programs and more annotators/contracts, see Programs.hs

For the language definition, see Syntax.hs

For the operational semantics, see Eval.hs (or EvalSubst.hs which is not used but follows the semantics from the thesis)

Tested with cabal version 1.24.0.0 and ghc 8.0.1
