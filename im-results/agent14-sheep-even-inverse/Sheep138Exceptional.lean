import Sheep138HighH

namespace Sheep138Exceptional

private theorem huge_power (j : Nat) (hj : 138 ≤ j) :
    9*j+22 < 2^(j-3) := by
  have hall (n : Nat) : 9*(138+n)+22 < 2^(135+n) := by
    induction n with
    | zero => decide
    | succ n ih =>
      have hp : 2^(135+(n+1))=2*2^(135+n) := by
        rw [show 135+(n+1)=(135+n)+1 by omega, Nat.pow_succ]
        omega
      have hpos : 0<2^(135+n) := Nat.pow_pos (by omega)
      rw [hp]
      omega
  have heq1 : 9*j+22=9*(138+(j-138))+22 := by omega
  have he : j-3=135+(j-138) := by omega
  have heq2 : 2^(j-3)=2^(135+(j-138)) := congrArg (fun n : Nat => 2^n) he
  rw [heq1, heq2]
  exact hall (j-138)

private theorem no_special_zero (j a : Nat) (hj : 138 ≤ j) :
    3*2^a+a+3 ≠ 2^j := by
  intro h
  by_cases hal : a ≤ j-2
  · have hp : 2^a ≤ 2^(j-2) :=
      Nat.pow_le_pow_right (by decide) hal
    have he : 2^j=4*2^(j-2) := by
      calc
        2^j = 2^((j-2)+2) := by congr 1; omega
        _ = 2^(j-2)*2^2 := by rw [Nat.pow_add]
        _ = 4*2^(j-2) := by simp [Nat.mul_comm]
    have hg := huge_power j hj
    have hsmall : a+3 < 2^(j-2) := by
      have hpowle : 2^(j-3) ≤ 2^(j-2) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega
    omega
  · have hal2 : j-1 ≤ a := by omega
    have hp : 2^(j-1) ≤ 2^a :=
      Nat.pow_le_pow_right (by decide) hal2
    have he : 2^j=2*2^(j-1) := by
      calc
        2^j = 2^((j-1)+1) := by congr 1; omega
        _ = 2^(j-1)*2 := by rw [Nat.pow_succ]
        _ = 2*2^(j-1) := by omega
    have hpos : 0<2^(j-1) := Nat.pow_pos (by omega)
    omega

private theorem no_special_one (j a : Nat) (hj : 138 ≤ j) :
    9*2^a+3*a+8 ≠ 2^(j+1) := by
  intro h
  by_cases hal : a ≤ j-3
  · have hp : 2^a ≤ 2^(j-3) :=
      Nat.pow_le_pow_right (by decide) hal
    have he : 2^(j+1)=16*2^(j-3) := by
      have hr : j+1=(j-3)+4 := by omega
      rw [hr,Nat.pow_add]
      omega
    have hg := huge_power j hj
    omega
  · have hal2 : j-2 ≤ a := by omega
    have hp : 2^(j-2) ≤ 2^a :=
      Nat.pow_le_pow_right (by decide) hal2
    have he : 2^(j+1)=8*2^(j-2) := by
      have hr : j+1=(j-2)+3 := by omega
      rw [hr,Nat.pow_add]
      omega
    have hpos : 0<2^(j-2) := Nat.pow_pos (by omega)
    omega

private theorem no_special_two (j a : Nat) (hj : 138 ≤ j) :
    27*2^a+9*a+22 ≠ 2^(j+2) := by
  intro h
  by_cases hal : a ≤ j-3
  · have hp : 2^a ≤ 2^(j-3) :=
      Nat.pow_le_pow_right (by decide) hal
    have he : 2^(j+2)=32*2^(j-3) := by
      have hr : j+2=(j-3)+5 := by omega
      rw [hr,Nat.pow_add]
      omega
    have hg := huge_power j hj
    omega
  · have hal2 : j-2 ≤ a := by omega
    have hp : 2^(j-2) ≤ 2^a :=
      Nat.pow_le_pow_right (by decide) hal2
    have he : 2^(j+2)=16*2^(j-2) := by
      have hr : j+2=(j-2)+4 := by omega
      rw [hr,Nat.pow_add]
      omega
    have hpos : 0<2^(j-2) := Nat.pow_pos (by omega)
    omega

/-- No special odd-part-three E edge may arrive at any r=138+4860k
power-of-two target, from any natural source. -/
theorem no_special_predecessor (k a h u : Nat)
    (hz : 3*2^a+a+3 = 1+2^h*u)
    (hy : 2^(138+4860*k)=1+3^h*u) : False := by
  let j := 138+4860*k
  have hj : 138 ≤ j := by dsimp [j]; omega
  have hh : h<3 := Sheep138HighH.root_predecessor_h_lt_three k h u hy
  have hh012 : h=0 ∨ h=1 ∨ h=2 := by omega
  rcases hh012 with h0 | h1 | h2
  · subst h
    have he : 3*2^a+a+3=2^j := by
      change 3*2^a+a+3=2^(138+4860*k)
      omega
    exact no_special_zero j a hj he
  · subst h
    have he : 9*2^a+3*a+8=2^(j+1) := by
      have hpow : 2^(j+1)=2*2^j := by rw [Nat.pow_succ]; omega
      dsimp [j] at hpow ⊢
      omega
    exact no_special_one j a hj he
  · subst h
    have he : 27*2^a+9*a+22=2^(j+2) := by
      have hpow : 2^(j+2)=4*2^j := by
        rw [show j+2=j+1+1 by omega,Nat.pow_succ,Nat.pow_succ]
        omega
      dsimp [j] at hpow ⊢
      omega
    exact no_special_two j a hj he

#print axioms no_special_predecessor
end Sheep138Exceptional
