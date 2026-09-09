import Definitions

/-!
# Proof data for the negation of DeVos Conjecture 6.10

The statement itself is kept in `devosNegation.lean` as `VertexAverageConjecture_false`. This file verifies the construction for the counterexample.
-/

namespace DeVos

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- Five vertices, two labels. Each entry lists all successors in that layer. -/
def exampleGraph : LabeledDigraph 5 2 := fun i v w =>
  match i.val, v.val with
  | 0, 0 => w == 1 || w == 4
  | 0, 1 => w == 0 || w == 3
  | 0, 2 => w == 1 || w == 4
  | 0, 3 => w == 0 || w == 4
  | 0, 4 => w == 2 || w == 3
  | 1, 0 => w == 4
  | 1, 1 => w == 4
  | 1, 2 => w == 1
  | 1, 3 => w == 0
  | 1, 4 => w == 1
  | _, _ => false

/-- Explicitly check that the underlying directed graph is loopless. -/
theorem example_loopless :
    ∀ (i : Fin 2) (v : Fin 5), exampleGraph i v v = false := by decide

/-- With two labels, every rainbow cycle would be a loop or a rainbow digon.
    This checks absence of rainbow digons in either label order. -/
theorem example_no_rainbow_digon :
    ∀ (v w : Fin 5),
      (exampleGraph 0 v w && exampleGraph 1 w v) = false ∧
      (exampleGraph 1 v w && exampleGraph 0 w v) = false := by decide

theorem example_no_increasing_cycle : NoIncreasingCycle exampleGraph := by
  unfold NoIncreasingCycle
  decide

theorem example_outdegrees :
    ∀ v : Fin 5, outdegree exampleGraph 0 v = 2 ∧
      outdegree exampleGraph 1 v = 1 := by decide

theorem example_minimum_outdegrees :
    minimumOutdegree exampleGraph 0 = 2 ∧
    minimumOutdegree exampleGraph 1 = 1 := by decide

theorem example_reachable_sets :
    (List.finRange 5).map (fun v =>
      ((List.finRange 5).filter (fun w =>
        reaches exampleGraph (List.finRange 2) v w)).map Fin.val) =
    [[0, 1, 4], [0, 1, 3, 4], [1, 2, 4], [0, 1, 3, 4], [0, 1, 2, 3, 4]] := by
  decide

theorem example_reachable_sizes :
    (List.finRange 5).map (reachCount exampleGraph) = [3, 4, 3, 4, 5] := by
  decide

theorem example_total_and_bound :
    totalReach exampleGraph = 19 ∧ proposedBound exampleGraph = 4 := by decide

theorem example_average : averageReach exampleGraph = (19 : Q) / 5 := by decide

theorem example_below_bound :
    averageReach exampleGraph < natQ (proposedBound exampleGraph) := by decide

end DeVos
