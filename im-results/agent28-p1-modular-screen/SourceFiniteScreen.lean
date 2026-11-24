import ModScreen
import WallListSource

namespace BB6.Agent28ModScreen
open BB6.Agent28 BB6.Agent28BitCarry BB6.Agent43WallListSource

theorem listRun_source_eq (n j k : Nat) (cs : List Nat) :
    listRun n j cs k = BB6WallCarry.carryStatesFrom n j cs k := by
  induction k generalizing j cs with
  | zero => rfl
  | succ k ih =>
      simp only [listRun, BB6WallCarry.carryStatesFrom]
      rw [ih]
      rfl

/-- All 14 ≤ n ≤ 10000 except the six listed survivors have no critical
right-five CountCone endpoint at ANY inverse depth or cost. -/
theorem source_finite_screen (n b m z : Nat) (hn : 14≤n) (hhi : n≤10000)
    (hs : survivor n=false) :
    ¬ CountCone (14*2^n-2*n-16) 3 b 5 m z := by
  by_cases he : n%2=0
  · obtain ⟨r,k,hr,hkn,⟨t,ht⟩,hempty⟩ :=
      certificate_of_non_survivor n hn hhi he hs
    apply source_no_right_five_of_no_prefix n b m z k hn hkn
    rw [ht]
    apply BB6WallCarry.noBitSubset_of_add_multiple r k t hr
    rw [← listRun_source_eq]
    exact hempty
  · exact source_no_right_five_of_no_prefix n b m z 0 hn (by omega)
      (noPrefix_odd n (by omega))

#print axioms source_finite_screen
end BB6.Agent28ModScreen
