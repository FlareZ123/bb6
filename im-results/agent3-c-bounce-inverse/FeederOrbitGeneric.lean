import FeederGeneric
import Agent3COrbitIff
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3

open BB6.Agent46

/-- The exact return-map precursor for every section feeder indexed by
    j=4t+1 with t>0; this is an all-natural-time orbit equivalence. -/
theorem generic_feeder_reach_iff (t : Nat) (ht : 1≤t) :
    CReach (16*t+3) (8*t+1) ↔ CReach (12*t) (10*t-1) := by
  constructor
  · rintro ⟨time,hr⟩
    cases time with
    | zero =>
      simp [CReach, BB6.Agent8Section.run] at hr
      omega
    | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at hr
      | some p =>
        rcases p with ⟨a,k⟩
        have hs : secNext (a,k)=some (16*t+3,8*t+1) := by
          simpa [BB6.Agent8Section.run,hp] using hr
        obtain ⟨ha,hk⟩ := (feeder_generic_iff t a k ht).mp hs
        exact ⟨n, by rwa [ha,hk] at hp⟩
  · rintro ⟨n,hr⟩
    have hpre : secNext (12*t,10*t-1)=some (16*t+3,8*t+1) :=
      (feeder_generic_iff t (12*t) (10*t-1) ht).mpr ⟨rfl,rfl⟩
    refine ⟨n+1, ?_⟩
    simpa [BB6.Agent8Section.run,hr,hpre]

/-- Two exact section steps reduce every t>0 member of the infinite
    one-left gate a=1,k=16t+4 to the nonhalting-branch precursor
    (12t,10t−1), with neither step bounded by a finite simulation. -/
theorem generic_one_gate_reach_iff (t : Nat) (ht : 1≤t) :
    CReach 1 (16*t+4) ↔ CReach (12*t) (10*t-1) := by
  have hj : 1≤4*t+1 := by omega
  have h := blank_one_four_iff_feeder (4*t+1) hj
  have ha : 4*(4*t+1)-1=16*t+3 := by omega
  have hk : 2*(4*t+1)-1=8*t+1 := by omega
  have htar : 4*(4*t+1)=16*t+4 := by omega
  rw [ha,hk,htar] at h
  exact h.trans (generic_feeder_reach_iff t ht)

#print axioms generic_feeder_reach_iff
#print axioms generic_one_gate_reach_iff
end BB6.Agent3
