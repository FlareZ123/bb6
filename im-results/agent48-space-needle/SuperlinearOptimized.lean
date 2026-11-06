import SuperlinearEnumerate

namespace BB6.Agent48.SuperlinearOptimal
open BB6.Agent48.SuperlinearEnum
open NeedleInverse

/-- Number of valuations tested for the chosen positive slope, before
potentially adding the isolated K13 exception. -/
def cutoff (K c : Nat) : Nat :=
  min ((K+2)/4+1) (max (4*((3:Nat)^c+1)) (K/c+1))

/-- Choose the least-cost positive slope among the first log2(K)+1 choices;
computational complexity is logarithmic in the terminal exponent K. -/
def bestSlope (K : Nat) : Nat :=
  (List.range (K.log2+1)).foldl
    (fun best i => if cutoff K (i+1) < cutoff K best then i+1 else best) 1

private theorem fold_pos (K : Nat) (xs : List Nat) (best : Nat) (hb : 1≤best) :
    1≤xs.foldl (fun b i => if cutoff K (i+1) < cutoff K b then i+1 else b) best := by
  induction xs generalizing best with
  | nil => simpa using hb
  | cons x xs ih =>
    simp only [List.foldl_cons]
    apply ih
    by_cases h : cutoff K (x+1)<cutoff K best
    · simp [h]
    · simp [h,hb]

private theorem fold_cutoff_min (K : Nat) (xs : List Nat) (best : Nat) :
    cutoff K (xs.foldl (fun b i => if cutoff K (i+1) < cutoff K b then i+1 else b) best) ≤ cutoff K best ∧
    ∀ i ∈ xs, cutoff K (xs.foldl (fun b j => if cutoff K (j+1) < cutoff K b then j+1 else b) best) ≤ cutoff K (i+1) := by
  induction xs generalizing best with
  | nil =>
    constructor
    · simp
    · intro i hi
      simp at hi
  | cons x xs ih =>
    let b' := if cutoff K (x+1)<cutoff K best then x+1 else best
    have hb : cutoff K b' ≤ cutoff K best := by
      by_cases h : cutoff K (x+1)<cutoff K best
      · simp [b',h]; omega
      · simp [b',h]
    have hx : cutoff K b' ≤ cutoff K (x+1) := by
      by_cases h : cutoff K (x+1)<cutoff K best
      · simp [b',h]
      · simp [b',h]; omega
    have hh := ih b'
    simp only [List.foldl_cons]
    constructor
    · change cutoff K (xs.foldl (fun b i => if cutoff K (i+1)<cutoff K b then i+1 else b) b') ≤ cutoff K best
      exact Nat.le_trans hh.1 hb
    · intro i hi
      change cutoff K (xs.foldl (fun b j => if cutoff K (j+1)<cutoff K b then j+1 else b) b') ≤ cutoff K (i+1)
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hmem
      · exact Nat.le_trans hh.1 hx
      · exact hh.2 i hmem

/-- The chosen slope minimizes the valuation cutoff among every c in the
explicit log2(K)+1 search range. -/
theorem bestSlope_minimal (K c : Nat) (hc : 1≤c) (hclt : c≤K.log2+1) :
    cutoff K (bestSlope K) ≤ cutoff K c := by
  let i := c-1
  have hi : i ∈ List.range (K.log2+1) := by
    apply List.mem_range.mpr
    dsimp [i]
    omega
  have hf : i+1=c := by dsimp [i]; omega
  have hbest := (fold_cutoff_min K (List.range (K.log2+1)) 1).2 i hi
  simpa only [bestSlope,hf] using hbest

theorem bestSlope_pos (K : Nat) : 1 ≤ bestSlope K := by
  exact fold_pos K _ 1 (by decide)

/-- The tested valuation list is exactly correct at every exponent, even
when a chosen slope is only a heuristic to minimize the search width. -/
def optimizedParents (K : Nat) : List (Nat × Nat) :=
  superlinearParents K (bestSlope K)

theorem optimizedParents_spec (q v K : Nat) :
    (v,q) ∈ optimizedParents K ↔ equation q v K := by
  exact superlinearParents_spec q v K (bestSlope K) (bestSlope_pos K)

#print axioms bestSlope_minimal
#print axioms bestSlope_pos
#print axioms optimizedParents_spec
end BB6.Agent48.SuperlinearOptimal
