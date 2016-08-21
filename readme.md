Master thesis implementation (Better Feedback for Incorrect Programs by Using Contracts)
====

This package is a prototype of the lambda-plus language and annotators as described in my master thesis. All modules are self-documented. To see the result of the annotators, run:

> cabal repl
> import Demo
> sort_correct
>


For student programs and more annotators/contracts, see Programs.hs

For the language definition, see Syntax.hs

For the operational semantics, see Eval.hs (or EvalSubst.hs which is not used but follows the semantics from the thesis)