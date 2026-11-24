import F418Arithmetic

namespace BB6.Agent32F418.EventSystem
open Arithmetic

/-- Extract the number of trailing binary zeroes and the tail beyond the first 1. -/
def splitOdd (N : Nat) : Nat × Nat :=
  if _h : N = 0 then (0,0)
  else if N % 2 = 1 then (0,N/2)
  else
    let (j,Q) := splitOdd (N/2)
    (j+1,Q)
termination_by N
decreasing_by omega

theorem splitOdd_spec (N : Nat) (hN : 0 < N) :
    N = 2^(splitOdd N).1 * (2*(splitOdd N).2+1) := by
  induction N using Nat.strongRecOn with
  | ind N ih =>
    by_cases h : N % 2 = 1
    · rw [splitOdd]
      simp [show N ≠ 0 by omega,h]
      omega
    · have hdiv : 0 < N/2 := by omega
      have hr := ih (N/2) (by omega) hdiv
      rcases he : splitOdd (N/2) with ⟨j,Q⟩
      rw [he] at hr
      dsimp at hr
      rw [splitOdd]
      simp [show N ≠ 0 by omega,h,he]
      rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2 (2*Q+1), ← Nat.mul_assoc]
      omega

theorem splitOdd_tail_lt (N : Nat) (hN : 0 < N) : (splitOdd N).2 < N := by
  have h := splitOdd_spec N hN
  have hp := Nat.two_pow_pos (splitOdd N).1
  have hh : 2*(splitOdd N).2+1 ≤ 2^(splitOdd N).1*(2*(splitOdd N).2+1) := by
    simpa using Nat.mul_le_mul_right (2*(splitOdd N).2+1) hp
  omega

/-- Empty shifted-left words are normalized to ordinary register states. -/
inductive State where
  | reg0 (N n w : Nat)
  | reg1 (n w : Nat)
  | shift2 (N a n w : Nat)
  | shift4 (N W : Nat)
  | shift1 (N n w : Nat)
  deriving Repr, DecidableEq

open State

def Safe : State → Prop
  | reg0 N n w => RightWidth n w ∧ N < n
  | reg1 n w => RightWidth n w ∧ NonPower (gap n w)
  | shift2 N a n w => 0 < N ∧ a ≤ 1 ∧ RightWidth n w ∧ N < n ∧ N < gap n w
  | shift4 N W => 0 < N ∧ N < 2^W ∧ NonPower N
  | shift1 N n w => 0 < N ∧ RightWidth n w ∧ N < n ∧ N < gap n w

def shift2OrReg1 (Q n w : Nat) : State := if Q = 0 then reg1 n w else shift2 Q 1 n w

def advance : State → Option State
  | reg0 N n w => some (shift2 (N+gap n w) 1 (2^w) (w+1))
  | reg1 n w => some (shift4 (gap n w) (w-1))
  | shift2 N a n w =>
    let (j,Q) := splitOdd N
    let e := (5*j+1)/2
    let n' := resetRight a (n+(2^j-1)) e
    let w' := w+e+2
    if j%2=0 then some (reg0 Q n' w') else some (shift2OrReg1 Q n' w')
  | shift4 N W =>
    let (j,Q) := splitOdd N
    let e := (5*j+4)/2
    let n' := resetRight 0 (2^W+(2^(j+1)-1)) e
    let w' := W+1+e+2
    if j%2=0 then some (shift1 Q n' w') else some (shift2 Q 0 n' w')
  | shift1 _ _ _ => none

theorem safe_shift2OrReg1 {Q n w : Nat} (hw : RightWidth n w) (hN : Q < n)
    (ht : Q < gap n w) (hn : NonPower (gap n w)) : Safe (shift2OrReg1 Q n w) := by
  unfold shift2OrReg1
  split
  · exact ⟨hw,hn⟩
  · exact ⟨by omega,by decide,hw,hN,ht⟩

theorem safe_advance {s s' : State} (hs : Safe s) (h : advance s = some s') : Safe s' := by
  cases s with
  | reg0 N n w =>
    obtain ⟨hw,hN⟩ := hs
    obtain ⟨hp,hlt,hw',ht⟩ := standard_zero_overflow hw hN
    simp [advance] at h
    subst s'
    exact ⟨hp,by decide,hw',hlt,ht⟩
  | reg1 n w =>
    obtain ⟨hw,hn⟩ := hs
    obtain ⟨hp,hlt,_,_,hN⟩ := standard_one_overflow hw hn
    simp [advance] at h
    subst s'
    exact ⟨hp,hlt,hN⟩
  | shift2 N a n w =>
    obtain ⟨hp,ha,hw,hN,ht⟩ := hs
    have hf := splitOdd_spec N hp
    rcases hj : splitOdd N with ⟨j,Q⟩
    rw [hj] at hf
    have hr := reset12_safe (e:=(5*j+1)/2) ha hw hN ht hf
    dsimp at hr
    obtain ⟨hw',hQ,ht',hn⟩ := hr
    simp only [advance,hj] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst s'
      exact ⟨hw',hQ⟩
    · simp only [Option.some.injEq] at h
      subst s'
      exact safe_shift2OrReg1 hw' hQ ht' hn
  | shift4 N W =>
    obtain ⟨hp,ht,hn⟩ := hs
    have hf := splitOdd_spec N hp
    rcases hj : splitOdd N with ⟨j,Q⟩
    rw [hj] at hf
    have hr := reset4_safe (e:=(5*j+4)/2) hf ht hn
    dsimp at hr
    obtain ⟨hw',hQ,hN,ht',_⟩ := hr
    simp only [advance,hj] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst s'
      exact ⟨hQ,hw',hN,ht'⟩
    · simp only [Option.some.injEq] at h
      subst s'
      exact ⟨hQ,by decide,hw',hN,ht'⟩
  | shift1 N n w => simp [advance] at h

def seed : State := reg1 39464 16

theorem seed_safe : Safe seed := by
  change RightWidth 39464 16 ∧ NonPower (gap 39464 16)
  constructor
  · unfold RightWidth; decide
  · exact ⟨3,1629,by decide,by decide⟩

def iterate : Nat → State → Option State
  | 0,s => some s
  | k+1,s => (advance s).bind (iterate k)

theorem safe_iterate {s s' : State} (hs : Safe s) {k : Nat} (h : iterate k s = some s') : Safe s' := by
  induction k generalizing s with
  | zero => simp [iterate] at h; subst s'; exact hs
  | succ k ih =>
    cases hh : advance s with
    | none => simp [iterate,hh] at h
    | some t => exact ih (safe_advance hs hh) (by simpa [iterate,hh] using h)

theorem seed_orbit_safe {k : Nat} {s : State} (h : iterate k seed = some s) : Safe s :=
  safe_iterate seed_safe h

/-- The arithmetic event system stops only at the d=1 collision.
    Whether this event is ever reached by the actual seed is the open question. -/
theorem advance_none_iff (s : State) : advance s = none ↔ ∃ N n w, s = shift1 N n w := by
  cases s <;> simp [advance]
  all_goals split <;> simp

#print axioms splitOdd_spec
#print axioms safe_advance
#print axioms seed_orbit_safe
#print axioms advance_none_iff
end BB6.Agent32F418.EventSystem
