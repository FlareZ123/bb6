import Lean
import Lean.Elab.Tactic.Omega
import HighDyadicOlderGateFast

namespace BB6.Agent11OlderGateRawCensus

open BB6.Agent11OlderGateFast

/-- The 322 high target pairs in Agent4's raw mass-2000 box:
    m=0, 0≤j≤247; m=1, 0≤j≤59; m=2, 0≤j≤12; m=3, j=0. -/
def rawHighPoints : List (Nat × Nat) :=
  (List.range 248).map (fun j => (j,0)) ++
  (List.range 60).map (fun j => (j,1)) ++
  (List.range 13).map (fun j => (j,2)) ++
  [(0,3)]

/-- The original finite implementation of the older guard. -/
def scanAllowedBool (j m : Nat) : Bool :=
  (List.range (2*m+1)).all (fun n => decide (¬gate n j m))

def rejectedPoints : List (Nat × Nat) :=
  rawHighPoints.filter (fun p => !(scanAllowedBool p.1 p.2))

theorem rawHighPoints_length : rawHighPoints.length=322 := by
  decide

/-- The finite scan covers every possible n because the gate itself
    requires n+4≤2*m+2. -/
theorem scanAllowedBool_iff (j m : Nat) :
    scanAllowedBool j m = true ↔ ∀ n, ¬gate n j m := by
  unfold scanAllowedBool
  rw [List.all_eq_true]
  constructor
  · intro h n
    by_cases hlt : n < 2*m+1
    · have hmem : n∈List.range (2*m+1) := List.mem_range.mpr hlt
      exact of_decide_eq_true (h n hmem)
    · intro hg
      rcases hg with ⟨hlim,_,_⟩
      omega
  · intro h n hn
    have hlt : n < 2*m+1 := List.mem_range.mp hn
    exact decide_eq_true_eq.mpr (h n)

/-- Exactly three of the 322 high pairs in this raw box are rejected
    by the older all-depth guard. -/
theorem rejectedPoints_exact :
    rejectedPoints = [(14,1),(30,1),(46,1)] := by
  decide

#print axioms scanAllowedBool_iff
#print axioms rejectedPoints_exact
end BB6.Agent11OlderGateRawCensus
