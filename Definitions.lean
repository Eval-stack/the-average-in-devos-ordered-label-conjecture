import Std
import Std.Internal.Rat

/-!
# Definitions for DeVos Conjecture 6.10

The average is taken over starting vertices, and the starting vertex itself is
counted because the paths may be trivial.

Labels are 0,...,k-1 (a harmless shift of 1,...,k). An ordered pair has at most
one edge, carrying any subset of the labels. Different layers may overlap;
oppositely directed edges are allowed.
-/

namespace DeVos

/-- `E i v w = true` means that the directed edge v -> w carries label i. -/
abbrev LabeledDigraph (n k : Nat) := Fin k → Fin n → Fin n → Bool

/-- Process the available labels in order. Either skip the next label, or
    use it on one edge and continue with the remaining labels.
    With no labels left, only the zero-edge walk is possible.
    On `List.finRange k`, this enumerates exactly strictly increasing walks. -/
def reaches {n k : Nat} (E : LabeledDigraph n k) :
    List (Fin k) → Fin n → Fin n → Bool
  | [], v, w => v == w
  | i :: is, v, w =>
      reaches E is v w ||
        (List.finRange n).any (fun u => E i v u && reaches E is u w)

/-- The same enumeration, requiring at least one edge. -/
def reachesNontrivially {n k : Nat} (E : LabeledDigraph n k) :
    List (Fin k) → Fin n → Fin n → Bool
  | [], _, _ => false
  | i :: is, v, w =>
      reachesNontrivially E is v w ||
        (List.finRange n).any (fun u => E i v u && reaches E is u w)

/-- No nonempty strictly increasing closed walk. Such a walk contains a
    strictly increasing directed cycle; conversely every such cycle is a
    nonempty closed walk. Under this condition all increasing walks are paths. -/
def NoIncreasingCycle {n k : Nat} (E : LabeledDigraph n k) : Prop :=
  ∀ v : Fin n, reachesNontrivially E (List.finRange k) v v = false

/-- Number of DISTINCT reachable endpoints, including the starting vertex. -/
def reachCount {n k : Nat} (E : LabeledDigraph n k) (v : Fin n) : Nat :=
  ((List.finRange n).filter (fun w => reaches E (List.finRange k) v w)).length

def outdegree {n k : Nat} (E : LabeledDigraph n k)
    (i : Fin k) (v : Fin n) : Nat :=
  ((List.finRange n).filter (E i v)).length

/-- The actual global minimum in the layer, not a stipulated lower bound.
    For n>0 the fold starts at n, an upper bound on every outdegree. -/
def minimumOutdegree {n k : Nat} (E : LabeledDigraph n k) (i : Fin k) : Nat :=
  ((List.finRange n).map (outdegree E i)).foldl Nat.min n

def totalReach {n k : Nat} (E : LabeledDigraph n k) : Nat :=
  ((List.finRange n).map (reachCount E)).foldl (· + ·) 0

def proposedBound {n k : Nat} (E : LabeledDigraph n k) : Nat :=
  1 + ((List.finRange k).map (minimumOutdegree E)).foldl (· + ·) 0

/-- Exact rational arithmetic from Lean's standard library; no floating point. -/
abbrev Q := Std.Internal.Rat

def natQ (a : Nat) : Q := Std.Internal.mkRat (Int.ofNat a) 1

def averageReach {n k : Nat} (E : LabeledDigraph n k) : Q :=
  natQ (totalReach E) / natQ n

/-- Insert an element in every possible position in a list. -/
def insertEverywhere {α : Type} (a : α) : List α → List (List α)
  | [] => [[a]]
  | x :: xs =>
      (a :: x :: xs) :: (insertEverywhere a xs).map (fun ys => x :: ys)

/-- Enumerate every ordering of a list. On `List.finRange k`, no ordering is
    duplicated because the labels are distinct. -/
def listPermutations {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => (listPermutations xs).flatMap (insertEverywhere x)

/-- Every linear order of the `k` edge labels. -/
def labelOrders (k : Nat) : List (List (Fin k)) :=
  listPermutations (List.finRange k)

/-- There is no nonempty increasing closed walk in any ordering of the labels.
    Equivalently, there is no rainbow directed cycle. -/
def NoIncreasingCycleInEveryOrder {n k : Nat}
    (E : LabeledDigraph n k) : Prop :=
  (labelOrders k).all (fun order =>
    (List.finRange n).all (fun v =>
      !(reachesNontrivially E order v v))) = true

/-- Number of distinct endpoints reachable from `v` when labels are processed
    in the specified order. -/
def reachCountInOrder {n k : Nat} (E : LabeledDigraph n k)
    (order : List (Fin k)) (v : Fin n) : Nat :=
  ((List.finRange n).filter (fun w => reaches E order v w)).length

/-- Total reachable-set size over all starting vertices and label orders. -/
def totalReachOverLabelOrders {n k : Nat} (E : LabeledDigraph n k) : Nat :=
  (labelOrders k).foldl
    (fun total order =>
      total + ((List.finRange n).map (reachCountInOrder E order)).foldl (· + ·) 0)
    0

/-- Exact average over both starting vertices and all label orders. -/
def averageReachOverLabelOrders {n k : Nat} (E : LabeledDigraph n k) : Q :=
  natQ (totalReachOverLabelOrders E) /
    natQ (n * (labelOrders k).length)

end DeVos
