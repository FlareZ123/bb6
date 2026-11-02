import EvenTargetExact
import FeederOrbitGeneric
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3

open BB6.Agent46

/-- Exact all-time blank-origin reachability inverse for the entire
    high odd-counter family. Every listed parent is a genuine source edge;
    all possible source branches and unbounded bounce depths are covered. -/
theorem high_target_reach_iff (t : Nat) (ht : 1≤t) :
    CReach (12*t) (10*t-1) ↔
      ∃ r u : Nat, 1≤u ∧ t=2*(4^r*u) ∧
        CReach (22*u-3) (32*(4^r*u)-(11*u+3+3*r)) := by
  constructor
  · rintro ⟨time,h⟩
    cases time with
    | zero =>
      simp [BB6.Agent8Section.run] at h
      omega
    | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none =>
        simp [BB6.Agent8Section.run,hp] at h
      | some p =>
        rcases p with ⟨a,k⟩
        have hs : secNext (a,k)=some (12*t,10*t-1) := by
          simpa [BB6.Agent8Section.run,hp] using h
        obtain ⟨r,u,hu,htEq,ha,hk⟩ :=
          (universal_target_inverse_iff t a k ht).mp hs
        exact ⟨r,u,hu,htEq,⟨n,by rwa [ha,hk] at hp⟩⟩
  · rintro ⟨r,u,hu,htEq,⟨n,hr⟩⟩
    have hpre : secNext
        (22*u-3,32*(4^r*u)-(11*u+3+3*r)) =
        some (24*(4^r*u),20*(4^r*u)-1) :=
      general_even_inverse_edge r u hu
    refine ⟨n+1,?_⟩
    rw [htEq]
    simpa [BB6.Agent8Section.run,hr,hpre] using hpre

/-- Combining the exact two-step low-counter feeder with complete
    high-counter inversion yields an all-time three-section inverse grammar
    for every low target (1,16t+4), t>=1. -/
theorem low_gate_all_parents_iff (t : Nat) (ht : 1≤t) :
    CReach 1 (16*t+4) ↔
      ∃ r u : Nat, 1≤u ∧ t=2*(4^r*u) ∧
        CReach (22*u-3) (32*(4^r*u)-(11*u+3+3*r)) :=
  (generic_one_gate_reach_iff t ht).trans (high_target_reach_iff t ht)

/-- Every odd t has no physical blank-origin low gate (1,16t+4),
    including all section times. -/
theorem low_gate_odd_t_excluded (t : Nat) (ht : 1≤t) (ho : t%2=1) :
    ¬CReach 1 (16*t+4) := by
  intro hr
  obtain ⟨r,u,_,hpar,_⟩ := (low_gate_all_parents_iff t ht).mp hr
  omega

#print axioms high_target_reach_iff
#print axioms low_gate_all_parents_iff
#print axioms low_gate_odd_t_excluded
end BB6.Agent3
