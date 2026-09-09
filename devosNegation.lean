import devosProofStrong
import devosProofWeak

/-!
# Negation of DeVos Conjecture 6.10

Sullivan, *A Summary of Results and Problems Related to the
Caccetta-Haggkvist Conjecture* (2006), Conjecture 6.10, p. 7.

This file contains both the translated conjecture and its refutation.
-/

namespace DeVos

/-- The general conjecture, explicitly under the uniform-start interpretation.
    No vertexwise bound or average over label orders is substituted here. -/
def VertexAverageConjecture : Prop :=
  ∀ (n k : Nat), 0 < n → ∀ E : LabeledDigraph n k,
    NoIncreasingCycle E → natQ (proposedBound E) ≤ averageReach E

/- the formal proof of this negation lies in devosProofStrong.lean -/
theorem VertexAverageConjecture_false : ¬ VertexAverageConjecture := by
  intro conjecture
  exact (conjecture 5 2 (by decide)
    exampleGraph example_no_increasing_cycle) example_below_bound

/-- A weaker variant that assumes there is no increasing cycle in any label
    order and averages the reachable-set size over all label orders as well as
    all starting vertices. -/
def VertexAverageConjectureWeak : Prop :=
  ∀ (n k : Nat), 0 < n → ∀ E : LabeledDigraph n k,
    NoIncreasingCycleInEveryOrder E →
      natQ (proposedBound E) ≤ averageReachOverLabelOrders E

/- the formal proof of the negation of the weaker formulation lies in devosProofWeak.lean -/
theorem VertexAverageConjectureWeak_false : ¬ VertexAverageConjectureWeak := by
  intro conjecture
  exact (conjecture 9 2 (by decide)
    exampleGraphWeak exampleWeak_no_increasing_cycle_in_every_order)
      exampleWeak_below_bound

end DeVos
