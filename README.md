# Reachability Logic

Reachability logic deals with proving that a certain postcondition is guaranteed to occur.
The core concept is the so called reachability triple:

`<P> S <Q>`

Meaning:

For precondition P after executing S, there exists a state that satisfies Q.

## Status

The Haskell code needs some extra work, but should provide the basic abilities described in the paper

## Usage

The implementation is written in Haskell, and can be compiled using `ghc`:

    ghc -O main

or all the examples can be inspected interactively using `ghci`

    ghci main
    :module +*Examples

A precondition can be calculated using the precondition function, for example:

    *Examples *Main> exploits (writeWrite, postW)
    [[b#8]⋈[e#8] ∧ [d#8]⋈[e#8] ∧ (!e == z),[d#8]⋈[e#8] ∧ [b#8]≐[e#8] ∧ (!a == z),[b#8]⋈[c#8] ∧ [d#8]≐[e#8] ∧ (!c == z),[b#8]≐[c#8] ∧ [d#8]≐[e#8] ∧ (!a == z)]

## Isabelle/HOL proofs

The file ExploitLogic.thy contain the Isabelle/HOL proofs, and can be loaded in Isabelle 2021.
