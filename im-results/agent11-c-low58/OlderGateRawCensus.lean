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

def candidateRejectedPoints : List (Nat × Nat) :=
  rawHighPoints.filter (fun p => !(candidateAllowedBool p.1 p.2))

theorem rawHighPoints_length : rawHighPoints.length=322 := by
  simp [rawHighPoints]

/-- The finite scan covers every possible n because the gate itself
    requires n+4≤2*m+2. -/
theorem scanAllowedBool_iff (j m : Nat) :
    scanAllowedBool j m = true ↔ ∀ n, ¬gate n j m := by
  unfold scanAllowedBool
  constructor
  · intro h n
    have hall : ∀ a ∈ List.range (2*m+1),
        decide (¬gate a j m)=true := List.all_eq_true.mp h
    by_cases hlt : n < 2*m+1
    · have hmem : n∈List.range (2*m+1) := List.mem_range.mpr hlt
      exact of_decide_eq_true (hall n hmem)
    · intro hg
      rcases hg with ⟨hlim,_,_⟩
      omega
  · intro h
    apply List.all_eq_true.mpr
    intro n hn
    exact decide_eq_true_eq.mpr (h n)

/-- The three excluded pairs each have the simple depth-zero witness. -/
theorem scan_matches_candidate (j m : Nat) :
    scanAllowedBool j m = candidateAllowedBool j m := by
  cases hs : scanAllowedBool j m with
  | false =>
    cases hc : candidateAllowedBool j m with
    | false => rfl
    | true =>
      have hall := (candidateAllowedBool_iff j m).mp hc
      have hscan := (scanAllowedBool_iff j m).mpr hall
      rw [hs] at hscan
      contradiction
  | true =>
    cases hc : candidateAllowedBool j m with
    | false =>
      have hall := (scanAllowedBool_iff j m).mp hs
      have hc' := (candidateAllowedBool_iff j m).mpr hall
      rw [hc] at hc'
      contradiction
    | true => rfl

theorem older_gate_witnesses :
    gate 0 14 1 ∧ gate 0 30 1 ∧ gate 0 46 1 := by
  decide

/-- Exactly three of the 322 high pairs in this raw box are rejected
    by the older all-depth guard. -/
theorem rejectedPoints_exact :
    rejectedPoints = [(14,1),(30,1),(46,1)] := by
  decide

theorem candidateRejectedPoints_exact :
    candidateRejectedPoints = [(14,1),(30,1),(46,1)] := by
  have hEq : scanAllowedBool = candidateAllowedBool := by
    funext j m
    exact scan_matches_candidate j m
  change rawHighPoints.filter (fun p => !(candidateAllowedBool p.1 p.2)) =
    [(14,1),(30,1),(46,1)]
  rw [← hEq]
  exact rejectedPoints_exact

#print axioms scanAllowedBool_iff
#print axioms scan_matches_candidate
#print axioms rejectedPoints_exact
#print axioms candidateRejectedPoints_exact
end BB6.Agent11OlderGateRawCensus
