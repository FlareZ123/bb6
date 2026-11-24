import CapBmo
import CapSieveSource
import CapMulti

namespace CapSieve.Bmo

theorem areach_iff_cap {s t : Nat} : AReach s t ↔ Cap.Reach s t := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ e ih => exact .tail ih (CapSieve.arc_iff.mp e)
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ e ih => exact .tail ih (CapSieve.arc_iff.mpr e)

theorem root_criterion {s : Nat} (hs : Cap.rootOf s=s) :
    (∃ i, AReach s (T i)) ↔ ∃ i, Cap.rootOf (Cap.halt i)=s := by
  constructor
  · rintro ⟨i,hi⟩
    refine ⟨i,?_⟩
    have h:=areach_iff_cap.mp hi
    rw [CapSieve.t_eq] at h
    exact (Cap.reach_from_root s _ hs).mp h
  · rintro ⟨i,hi⟩
    refine ⟨i,?_⟩
    apply areach_iff_cap.mpr
    rw [CapSieve.t_eq]
    exact (Cap.reach_from_root s _ hs).mpr hi

theorem seed_three_criterion : (∃ n, Halt (orbit ⟨0,3⟩ n)) ↔
    ∃ i, Cap.rootOf (Cap.halt i)=2 := seed_three_root.trans (root_criterion Cap.root_two)

theorem seed_five_criterion : (∃ n, Halt (orbit ⟨0,5⟩ n)) ↔
    ∃ i, Cap.rootOf (Cap.halt i)=1 := seed_five_root.trans (root_criterion Cap.root_one)

theorem seed_six_criterion : (∃ n, Halt (orbit ⟨0,6⟩ n)) ↔
    ∃ i, Cap.rootOf (Cap.halt i)=3 := seed_six_root.trans (root_criterion Cap.root_three)

#print axioms seed_three_criterion
#print axioms seed_five_criterion
#print axioms seed_six_criterion
end CapSieve.Bmo
