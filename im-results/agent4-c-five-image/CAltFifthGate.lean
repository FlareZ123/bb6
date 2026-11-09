import CAltFifthSource
import Lean.Elab.Tactic.Omega
namespace BB6.Agent4Five
open BB6.Agent46

private theorem power_margin (q : Nat) :
    3*(q+22)+100 ≤ (2:Nat)^(2*(q+22)+2) := by
  induction q with
  | zero => decide
  | succ q ih =>
      have he : 2*((q+1)+22)+2=(2*(q+22)+2)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

/-- Every source-authentic stopping equation in this full congruence
    strip falls into the forbidden strict fourth/fifth image lattice. -/
private theorem general_high_stop_lattice (w m k : Nat)
    (hpair : (m+32*w)%128=22)
    (hstop : k+(32*w+43)+3*m+5 =
      (2:Nat)^(2*m+2)*((32*w+43)+3)) :
    ∃ t, 2≤t ∧ (w+t)%2=0 ∧ k=64*t+14 := by
  let j := 32*w+43
  let P := (2:Nat)^(2*m+2)
  have hm32 : m%32=22 := by omega
  have hm : 22≤m := by omega
  have hj : 43≤j := by dsimp [j]; omega
  have hst : k+j+3*m+5=P*(j+3) := by simpa only [j,P] using hstop
  have hpow : 128 ∣ P := by
    have hd : (2:Nat)^7 ∣ (2:Nat)^(2*m+2) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa [P,show (2:Nat)^7=128 by decide] using hd
  obtain ⟨z,hz⟩ := hpow
  have hzero : (k+j+3*m+5)%128=0 := by
    apply Nat.mod_eq_zero_of_dvd
    refine ⟨z*(j+3),?_⟩
    calc
      k+j+3*m+5=P*(j+3) := hst
      _=(128*z)*(j+3) := by rw [hz]
      _=128*(z*(j+3)) := by ac_rfl
  have hres : (k+64*w+114)%128=0 := by
    dsimp [j] at hzero
    omega
  have hp_bound : 3*m+100≤P := by
    have h := power_margin (m-22)
    have he : m-22+22=m := by omega
    rw [he] at h
    exact h
  have hp_pos : 1≤P := by omega
  have hjmul : j≤P*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp_pos
  have hproduct : P*(j+3)=P*j+3*P := by rw [Nat.mul_add]; ac_rfl
  have hlarge : 142≤k := by
    rw [hproduct] at hst
    omega
  have hkmod : k%64=14 := by omega
  let t := (k-14)/64
  have hkt : k=64*t+14 := by dsimp [t]; omega
  have hpar : (w+t)%2=0 := by dsimp [t]; omega
  have ht : 2≤t := by dsimp [t]; omega
  exact ⟨t,ht,hpar,hkt⟩

/-- Entire authentic Machine C high stopping modulo-128 strip is
    blank-unreachable, uniformly over all its unbounded parameters. -/
theorem high_stop_fifth_mod128_unreachable (w m k time : Nat)
    (hpair : (m+32*w)%128=22)
    (hstop : k+(32*w+43)+3*m+5 =
      (2:Nat)^(2*m+2)*((32*w+43)+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*(32*w+43)+3,k) := by
  obtain ⟨t,ht,hpar,hkt⟩ := general_high_stop_lattice w m k hpair hstop
  have hx : 2*(32*w+43)+3=64*w+89 := by omega
  rw [hx,hkt]
  exact fifth_blank_unreachable w t time ht hpar

/-- A simple infinite two-parameter arithmetic progression within the strip. -/
theorem high_stop_fifth_blank_unreachable (w h k time : Nat)
    (hstop : k+(32*w+43)+3*(22+96*w+128*h)+5 =
      (2:Nat)^(2*(22+96*w+128*h)+2)*((32*w+43)+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*(32*w+43)+3,k) := by
  exact high_stop_fifth_mod128_unreachable w (22+96*w+128*h) k time
    (by omega) hstop

#print axioms high_stop_fifth_mod128_unreachable
end BB6.Agent4Five
