# the-average-in-devos-ordered-label-conjecture

This repository seeks to formalize the average in Devos' conjecture, which is stated as Conjecture 6.10 of Sullivan's 2006 survey:
https://aimath.org/WWN/caccetta/caccetta.pdf

We resolve the conjecture in the negative with a five-vertex counterexample.
We also refute a weaker variant that averages over every ordering of the edge
labels, using a nine-vertex counterexample whose two label layers are identical.

`Definitions.lean` contains the standard definitions.
`devosNegation.lean` defines `VertexAverageConjecture` and
`VertexAverageConjectureWeak`, and proves both negations.
`devosProofStrong.lean` verifies the five-vertex counterexample to the original
conjecture. `devosProofWeak.lean` verifies the nine-vertex counterexample to the
label-order-averaged variant.

The five-vertex and nine-vertex construction ideas were found by Evan Li (Evl012@ucsd.edu). Majority of the credit goes to him.
Parts of the proof of the construction and the eventual lean formalization was done by Lily Zhang (pink@berkeley.edu).

The arxiv write-up will be done mostly by Evan and is coming soon...

## Reproduce

Install Lean 4.19.0 using your usual Lean installation method. From this directory run in powershell:

```sh
lake build
```
The file compiled successfully with Lean 4.19.0 during our session. There are no `native_decide`, `sorry`, `admit`, or user-added axioms. The dependency `propext` is Lean's standard propositional extensionality axiom.
