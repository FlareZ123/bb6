import BulkRuns
import Lean.Elab.Tactic.Omega

namespace BB6.Agent2F321LastFarExact
open BB6.Agent2F321Bulk
open BB6.Agent2F321Diagonal

private theorem pow_two_lower (n : Nat) : n+1 ≤ 2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.pow_succ]
      omega

/-- A nonnegative endpoint and the two exact high-block balances suffice
    for every individual High guard, without replaying the block. -/
theorem highRun_of_balances {n a d A D : Nat}
    (hs : A+D = a+d+n)
    (hd : D+3 = 2^n*(d+3)) : HighRun n a d A D := by
  induction n generalizing a d with
  | zero =>
      simp at hd hs
      have he : D = d := by omega
      have ha : A = a := by omega
      subst D; subst A
      exact HighRun.nil _ _
  | succ n ih =>
      have hp := pow_two_lower (n+1)
      have hm := Nat.mul_le_mul_right (d+3) hp
      have hmn : n ≤ n*(d+3) := by
        have ht := Nat.mul_le_mul_left n (show 1 ≤ d+3 by omega)
        simpa using ht
      have hdist : (n+1+1)*(d+3) = n*(d+3)+2*(d+3) := by
        simp only [Nat.add_mul, Nat.one_mul]
        omega
      rw [hdist, ← hd] at hm
      have hg : d+2 ≤ a := by omega
      apply HighRun.step hg
      apply ih
      · omega
      · rw [Nat.pow_succ] at hd
        have hmul : 2^n* (2*d+3+3) = (2^n*2)*(d+3) := by
          rw [show 2*d+3+3=2*(d+3) by omega, Nat.mul_assoc]
        rw [hmul]
        exact hd

/-- A final Far feeder followed by exactly b High moves to the terminal gate. -/
def Feeder (b a d t : Nat) : Prop :=
  a < d ∧ 3*a+1 ≤ d ∧ HighRun b (4*a+6) (d-3*a) (t+1) t

/-- Complete, subtraction-free arithmetic characterization of a terminal
    last-Far feeder. z is the shifted second counter immediately after Far. -/
theorem feeder_iff (b a d t : Nat) : Feeder b a d t ↔
    ∃ z : Nat, 4 ≤ z ∧ d+3 = 3*a+z ∧
      t+3 = 2^b*z ∧ 4*a+z+b+8 = 2*(t+3) := by
  constructor
  · rintro ⟨h1,h2,hh⟩
    have hc := high_run_coordinates hh
    unfold X Y at hc
    have hpow : 2^b * (2*(d-3*a+3)) = 2*(2^b*(d-3*a+3)) := by ac_rfl
    rw [hpow] at hc
    exact ⟨d-3*a+3,by omega,by omega,by omega,by omega⟩
  · rintro ⟨z,hz,hd,ht,hs⟩
    refine ⟨by omega,by omega,?_⟩
    apply highRun_of_balances
    · omega
    · have he : d-3*a+3=z := by omega
      rw [he]
      exact ht

/-- The exact last-Far congruence modulo four. It strengthens the previously
    established parity-only law, for every trailing High count including zero. -/
theorem feeder_mod4 {b a d t : Nat} (hf : Feeder b a d t) :
    ∃ z : Nat, 4 ≤ z ∧ t+3=2^b*z ∧ (z+b)%4=0 := by
  rcases (feeder_iff b a d t).mp hf with ⟨z,hz,hd,ht,hs⟩
  refine ⟨z,hz,ht,?_⟩
  cases b with
  | zero =>
      simp at ht
      omega
  | succ b =>
      rw [Nat.pow_succ] at ht
      have hm : 2*(t+3) = 4*(2^b*z) := by
        rw [ht]
        calc
          2*(2^b*2*z) = (2*2)*(2^b*z) := by ac_rfl
          _ = 4*(2^b*z) := rfl
      omega

/-- Complete candidate generator for a terminal parameter and a fixed final
    High count. No search over predecessor counters is necessary. -/
theorem feeder_exists_iff (b t : Nat) : (∃ a d, Feeder b a d t) ↔
    ∃ z : Nat, 4 ≤ z ∧ t+3=2^b*z ∧ z+b+8 ≤ 2*(t+3) ∧
      (z+b)%4=0 := by
  constructor
  · rintro ⟨a,d,hf⟩
    rcases (feeder_iff b a d t).mp hf with ⟨z,hz,hd,ht,hs⟩
    rcases feeder_mod4 hf with ⟨w,hw,hwt,hm⟩
    have hp : 0 < 2^b := Nat.pow_pos (by decide)
    have hzw : z=w := Nat.eq_of_mul_eq_mul_left hp (ht.symm.trans hwt)
    subst w
    exact ⟨z,hz,ht,by omega,hm⟩
  · rintro ⟨z,hz,ht,hbound,hm⟩
    have hmod : (2*(t+3))%4=0 := by
      cases b with
      | zero => simp at ht; omega
      | succ b =>
          rw [Nat.pow_succ] at ht
          have he : 2*(t+3)=4*(2^b*z) := by
            rw [ht]
            calc
              2*(2^b*2*z) = (2*2)*(2^b*z) := by ac_rfl
              _ = 4*(2^b*z) := rfl
          omega
    let a := (2*(t+3)-(z+b+8))/4
    let d := 3*a+z-3
    have ha : 4*a+z+b+8=2*(t+3) := by
      dsimp [a]
      omega
    exact ⟨a,d,(feeder_iff b a d t).mpr ⟨z,hz,by dsimp [d]; omega,ht,ha⟩⟩

/-- For fixed terminal t and trailing length b there is at most one feeder. -/
theorem feeder_unique {b t a d A D : Nat}
    (h1 : Feeder b a d t) (h2 : Feeder b A D t) : a=A ∧ d=D := by
  rcases (feeder_iff b a d t).mp h1 with ⟨z,hz,hd,ht,hs⟩
  rcases (feeder_iff b A D t).mp h2 with ⟨w,hw,hD,hT,hS⟩
  have hp : 0 < 2^b := Nat.pow_pos (by decide)
  have hzw : z=w := Nat.eq_of_mul_eq_mul_left hp (ht.symm.trans hT)
  omega

#print axioms highRun_of_balances
#print axioms feeder_iff
#print axioms feeder_mod4
#print axioms feeder_exists_iff
#print axioms feeder_unique
end BB6.Agent2F321LastFarExact
