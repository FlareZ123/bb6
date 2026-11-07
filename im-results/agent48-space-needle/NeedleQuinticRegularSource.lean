import SpaceNeedleFifthRoot
import NeedleQuinticRegular

namespace BB6.Agent48.SpaceNeedleFifthRegularRoot
open BusyBeaver
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle

/-- Exact original raw-machine blank-tape halting iff a genuine blank-root
    high-level counter occurs in the finite fifth-linear exception-free
    terminal inverse list at some exponent. All-time reachability is still
    an unbounded existential and remains open. -/
theorem raw_halts_iff_reaches_regular_list :
    IsHalt target ↔
      ∃ k q v : Nat,
        ReachN (oddTower q v) ∧
        (v,q) ∈ NeedleQuinticRegular.parents (k+1) := by
  rw [BB6.Agent48.SpaceNeedleFifthRoot.raw_halts_iff_reaches_fifth_regular]
  constructor
  · rintro ⟨k,q,v,hr,hlist,hbound⟩
    have he := (NeedleQuinticEnum.quinticParents_spec q v (k+1)).mp hlist
    refine ⟨k,q,v,hr,?_⟩
    exact (NeedleQuinticRegular.parents_spec q v (k+1)).mpr
      ⟨he,by omega⟩
  · rintro ⟨k,q,v,hr,hlist⟩
    obtain ⟨he,hbound⟩ :=
      (NeedleQuinticRegular.parents_spec q v (k+1)).mp hlist
    exact ⟨k,q,v,hr,
      (NeedleQuinticEnum.quinticParents_spec q v (k+1)).mpr he,
      by omega⟩

#print axioms raw_halts_iff_reaches_regular_list
end BB6.Agent48.SpaceNeedleFifthRegularRoot
