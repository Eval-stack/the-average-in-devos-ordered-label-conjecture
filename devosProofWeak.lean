import Definitions

/-!
# Proof data for the weak, label-order-averaged conjecture

The statement itself is kept in `devosNegation.lean` as `VertexAverageConjectureWeak_false`. This file verifies the
nine-vertex construction used to refute it.
-/

namespace DeVos

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- Nine vertices and two identical label layers, both equal to the oriented
    graph described by the successor sets below. -/
def exampleGraphWeak : LabeledDigraph 9 2 := fun _ v w =>
  match v.val with
  | 0 => w == 1 || w == 3 || w == 4
  | 1 => w == 2 || w == 3 || w == 4
  | 2 => w == 0 || w == 3 || w == 4
  | 3 | 4 => w == 5 || w == 6 || w == 7
  | 5 | 6 | 7 | 8 => w == 0 || w == 1 || w == 2
  | _ => false

/-- The two labeled layers are identical. -/
theorem exampleWeak_layers_equal :
    ∀ (v w : Fin 9), exampleGraphWeak 0 v w = exampleGraphWeak 1 v w := by
  decide

/-- Explicitly check that the underlying directed graph is loopless. -/
theorem exampleWeak_loopless :
    ∀ (i : Fin 2) (v : Fin 9), exampleGraphWeak i v v = false := by decide

/-- Explicitly check that the common layer is oriented: no ordered pair occurs
    in both directions. -/
theorem exampleWeak_no_digon :
    ∀ (i j : Fin 2) (v w : Fin 9),
      (exampleGraphWeak i v w && exampleGraphWeak j w v) = false := by decide

theorem exampleWeak_label_orders :
    (labelOrders 2).map (fun order => order.map Fin.val) = [[0, 1], [1, 0]] := by
  decide

theorem exampleWeak_no_increasing_cycle_in_every_order :
    NoIncreasingCycleInEveryOrder exampleGraphWeak := by
  unfold NoIncreasingCycleInEveryOrder
  decide

theorem exampleWeak_outdegrees :
    ∀ (i : Fin 2) (v : Fin 9), outdegree exampleGraphWeak i v = 3 := by decide

theorem exampleWeak_minimum_outdegrees :
    ∀ i : Fin 2, minimumOutdegree exampleGraphWeak i = 3 := by decide

theorem exampleWeak_reachable_sizes_in_each_order :
    (labelOrders 2).map (fun order =>
      (List.finRange 9).map (reachCountInOrder exampleGraphWeak order)) =
    [[8, 8, 8, 7, 7, 6, 6, 6, 6],
     [8, 8, 8, 7, 7, 6, 6, 6, 6]] := by
  decide

theorem exampleWeak_total_and_bound :
    totalReachOverLabelOrders exampleGraphWeak = 124 ∧
      proposedBound exampleGraphWeak = 7 := by decide

theorem exampleWeak_average :
    averageReachOverLabelOrders exampleGraphWeak = (62 : Q) / 9 := by decide

theorem exampleWeak_below_bound :
    averageReachOverLabelOrders exampleGraphWeak <
      natQ (proposedBound exampleGraphWeak) := by decide

end DeVos
