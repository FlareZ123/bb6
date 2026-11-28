import Raw34EarlyHaltersSound
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Five previously completely unclassified three-slot Raw34 cylinders:
D1/C1/B1 all fixed, and five other rows arbitrary, including HALT.
A direct first-undefined-query analysis shows all five halt after 9,
11, or 12 ordinary transitions on the genuine blank tape. Each contains
25^5 = 9,765,625 physical completions. They lie entirely outside
the 3,087 old sources + ten graph masks + E/F counters + 1,067 early
halts (see rank_live_nonD1RD.mjs, CI 46119443983).
-/
namespace BB6.Agent40Raw34LateHalters
open BB6Coverage BB6.Agent23Raw34Next
open BB6.Agent40Raw34EarlyHalters

def witnesses : List Witness := [
  ⟨[21,0,22,15,11,1,16,14,0,0,0,0], .halt 12⟩,
  ⟨[21,0,22,23,11,1,16,14,0,0,0,0], .halt 9⟩,
  ⟨[21,0,22,1,11,5,16,15,0,0,0,0], .halt 9⟩,
  ⟨[21,0,22,1,11,17,16,15,0,0,0,0], .halt 9⟩,
  ⟨[21,0,22,1,11,23,16,15,0,0,0,0], .halt 11⟩
]

theorem count : witnesses.length = 5 := by decide
theorem checked : witnesses.all check = true := by decide
theorem short : witnesses.all (isShortHalt 13) = true := by decide

/-- Exact physical halt under any total completion; ≤13 attempted steps. -/
theorem all_halt (w : Witness) (hw : w ∈ witnesses)
    (m : Machine) (hm : compatible (table w.codes) m) :
    ∃ n : Nat, n+1 ≤ 13 ∧ HaltsAfter m n :=
  short_halt_sound 13 w
    (List.all_eq_true.mp short w hw)
    (List.all_eq_true.mp checked w hw) m hm

/-- The same genuine halt gives a correctly weighted finite score bound. -/
theorem all_weighted (w : Witness) (hw : w ∈ witnesses) :
    ∀ m, compatible (table w.codes) m → WeightedBound 32 m :=
  check_sound w (List.all_eq_true.mp checked w hw)

#print axioms count
#print axioms checked
#print axioms short
#print axioms all_halt
#print axioms all_weighted
end BB6.Agent40Raw34LateHalters
