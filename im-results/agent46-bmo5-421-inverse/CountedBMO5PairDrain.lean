import CountedBMO5Pair
import Counted421ClosedCost

namespace CountedBMO5Pair
set_option maxHeartbeats 1000000

open Counted421 (regularCost terminalCost specialCost resetCost fastD fastScore)

def cfg (x : Nat) := A2 0 1 (2*(x-2))

def pairDrainCost (r c : Nat) : Nat :=
  if r≤c then 9+regularCost r c
  else if r=c+1 then 4*c*c+24*c+30
  else if r=c+2 then 9+specialCost c
  else resetCost c+pairDrainCost (r-c-3) (2*c+4)
termination_by r
decreasing_by omega

macro "pairpoly" : tactic => `(tactic| (simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm,Nat.mul_zero,Nat.zero_mul,Nat.mul_one,Nat.one_mul,Nat.add_zero,Nat.zero_add] at *; simp only [Nat.reduceMul, ←Nat.mul_assoc] at *; omega))

theorem regular_exact (r d : Nat) :
    run (9+regularCost r (r+d)) (A2 0 (r+d) (2*r))=some (cfg (3*r+(r+d)+7)) := by
  cases r with
  | zero =>
    simp only [Nat.zero_add,Nat.mul_zero,cfg]
    rw [show 9+regularCost 0 d=14*d+87 by simp [regularCost]; omega,show 2*(d+7-2)=2*d+10 by omega]
    exact zero d
  | succ k =>
    have h1 := diagonal_many 0 d 0 (k+1)
    have h2 := zeroSucc (2*k+1) d
    have h3 := one (2*k+1) d
    rw [show 2*k+1+1=0+2*(k+1) by omega] at h2
    have h := seq (seq h1 h2) h3
    have hc : diagCost 0 (k+1)+2+(4*(2*k+1)*(2*k+1)+4*(2*k+1)*d+44*(2*k+1)+18*d+125)=9+regularCost (k+1) (k+1+d) := by
      simp only [diagCost,regularCost,Nat.add_sub_cancel_left]
      pairpoly
    simpa only [hc,Nat.add_comm d (k+1),Nat.zero_add,cfg,show 4*(2*k+1)+2*d+14=2*(3*(k+1)+(k+1+d)+7-2) by omega] using h

theorem drain_exact (r c : Nat) :
    Exact (A2 0 c (2*r)) (pairDrainCost r c) ((Cap.drain r c).map cfg) := by
  induction r using Nat.strongRecOn generalizing c with
  | ind r ih =>
    rw [pairDrainCost,Cap.drain]
    split
    next hr =>
      obtain ⟨d,rfl⟩ : ∃ d,c=r+d := ⟨c-r,by omega⟩
      exact regular_exact r d
    next hr =>
      split
      next he =>
        subst r
        have h1 := diagonal_many 0 0 2 c
        simp only [Nat.zero_add] at h1
        have h2 := halt_exact (2*c)
        have hc : diagCost 0 c+(8*(2*c)+30)=4*c*c+24*c+30 := by unfold diagCost; pairpoly
        simpa only [Option.map_none,hc,Nat.zero_add,show 2+2*c=2*(c+1) by omega] using exact_seq h1 h2
      next he =>
        split
        next hf =>
          subst r
          have h1 := diagonal_many 0 0 4 c
          simp only [Nat.zero_add] at h1
          have h2 := four (2*c)
          have hc : diagCost 0 c+(14*(2*c)+91)=9+specialCost c := by unfold diagCost specialCost; pairpoly
          simpa only [Option.map_some,Exact,hc,Nat.zero_add,cfg,show 4+2*c=2*(c+2) by omega,show 2*(2*c+8-2)=2*(2*c)+12 by omega] using seq h1 h2
        next hf =>
          have h1 := diagonal_many 0 0 (2*(r-c-3)+6) c
          simp only [Nat.zero_add] at h1
          have h2 := restart (2*c) (2*(r-c-3))
          have h3 := ih (r-c-3) (by omega) (2*c+4)
          have hc : diagCost 0 c+(8*(2*c)+34)=resetCost c := by unfold diagCost resetCost; pairpoly
          simpa only [hc,Nat.zero_add,show 2*(r-c-3)+6+2*c=2*r by omega] using exact_seq (seq h1 h2) h3

theorem shared_drain_cost (r c : Nat) :
    pairDrainCost r c+(if (Cap.drain r c).isNone then 12 else 0)=9+fastD r c := by
  induction r using Nat.strongRecOn generalizing c with
  | ind r ih =>
    rw [pairDrainCost,Cap.drain,fastD]
    split
    next h => simp
    next h =>
      split
      next h1 => simp [terminalCost]; omega
      next h1 =>
        split
        next h2 => simp
        next h2 =>
          have h3 := ih (r-c-3) (by omega) (2*c+4)
          omega

theorem section_success {x y : Nat} (hx : 2≤x) (he : Cap.f x=some y) :
    run (fastScore x) (cfg x)=some (cfg y) := by
  have h : Cap.drain (x-2) 1=some y := by simpa [Cap.f,show x≠0 by omega,show x≠1 by omega] using he
  have hc := shared_drain_cost (x-2) 1
  rw [h] at hc
  simp at hc
  have hh := drain_exact (x-2) 1
  rw [h,hc] at hh
  simpa [fastScore,show x≠0 by omega,show x≠1 by omega,cfg,Exact] using hh

theorem section_terminal {x : Nat} (hx : 2≤x) (he : Cap.f x=none) :
    ∃ t, fastScore x=t+12 ∧ Exact (cfg x) t none := by
  have h : Cap.drain (x-2) 1=none := by simpa [Cap.f,show x≠0 by omega,show x≠1 by omega] using he
  have hc := shared_drain_cost (x-2) 1
  rw [h] at hc
  simp at hc
  have hh := drain_exact (x-2) 1
  rw [h] at hh
  refine ⟨pairDrainCost (x-2) 1,?_,hh⟩
  simpa [fastScore,show x≠0 by omega,show x≠1 by omega] using hc.symm

#print axioms drain_exact
#print axioms shared_drain_cost
#print axioms section_success
#print axioms section_terminal
end CountedBMO5Pair
