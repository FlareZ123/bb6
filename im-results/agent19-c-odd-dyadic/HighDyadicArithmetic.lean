import Lean.Elab.Tactic.Omega

namespace BB6.Agent19HighDyadic

theorem eight_power_bound (m : Nat) (hm : 1≤m) :
    8*m+8≤2^(2*m+2) := by
  induction m with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => decide
    | succ n =>
      have hi : 8*(n+1)+8≤2^(2*(n+1)+2) := ih (by omega)
      have he : 2*(n+1+1)+2=(2*(n+1)+2)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

private theorem high_stop_big (j m k : Nat)
    (hm : 3≤m)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    50≤k := by
  have hp := eight_power_bound m (by omega)
  have hjp : j ≤ 2^(2*m+2)*j := by
    have hp1 : 1≤2^(2*m+2) := Nat.pow_pos (by decide)
    simpa using Nat.mul_le_mul_right j hp1
  have h3p : 3*(8*m+8) ≤ 3*2^(2*m+2) := by omega
  rw [Nat.mul_add] at hstop
  omega

private theorem high_stop_multiple64 (j m k : Nat)
    (hm : 3≤m)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ∃ q, k+j+3*m+5=64*q := by
  have hpow : (2:Nat)^6 ∣ (2:Nat)^(2*m+2) :=
    Nat.pow_dvd_pow 2 (by omega)
  have h64 : 64 ∣ (2:Nat)^(2*m+2) := by
    simpa only [show (2:Nat)^6=64 by decide] using hpow
  rcases h64 with ⟨z,hz⟩
  refine ⟨z*(j+3),?_⟩
  calc
    k+j+3*m+5=2^(2*m+2)*(j+3) := hstop
    _ = 64*(z*(j+3)) := by rw [hz]; simp only [Nat.mul_assoc]

private theorem high_arithmetic
    (j m k q : Nat)
    (hm4 : m % 4 = 3)
    (hpair : (j + 9*m + 14) % 64 = 48)
    (hstop64 : k+j+3*m+5 = 64*q)
    (hkbig : 50 ≤ k) :
    let x := 2*j+3
    let a := (x+k-4)/2
    let b := (x+3*k-10)/4
    let u := (b+2)/4
    k%2=1 ∧ 5≤k ∧ (x+k)%8=4 ∧ 24≤x+k ∧
    x+k=2*a+4 ∧ x+3*k=4*b+10 ∧
    b+2=4*u ∧ u%4=1 ∧ 9≤u ∧
    (a+2*b+8)%8=0 := by
  dsimp
  omega

/-- Pure Presburger and power arithmetic. For the high stopping target,
    the unique odd/odd inverse enters the depth-two six-cone. -/
theorem finalArithmetic (j m k : Nat) (hm3 : 3≤m)
  (hm4 : m%4=3) (hpair : (j+9*m+14)%64=48)
  (hstop : k+j+3*m+5=2^(2*m+2)*(j+3)) :
  let x := 2*j+3
  let a := (x+k-4)/2
  let b := (x+3*k-10)/4
  let u := (b+2)/4
  k%2=1 ∧ 5≤k ∧ (x+k)%8=4 ∧ 24≤x+k ∧
  x+k=2*a+4 ∧ x+3*k=4*b+10 ∧
  b+2=4*u ∧ u%4=1 ∧ 9≤u ∧
  (a+2*b+8)%8=0 := by
  obtain ⟨q,hq⟩ := high_stop_multiple64 j m k hm3 hstop
  exact high_arithmetic j m k q hm4 hpair hq
    (high_stop_big j m k hm3 hstop)

#print axioms finalArithmetic
end BB6.Agent19HighDyadic
