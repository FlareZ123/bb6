import Std
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
namespace SheepA6Boost

private theorem pow4_729 : (4:Nat)^729%43=4 := by
  have he : 729 = 7*104+1 := by decide
  rw [he,Nat.pow_add,Nat.mul_mod,Nat.pow_mul,Nat.pow_mod]

private theorem four_six (m : Nat) : (4:Nat)^(3^(6*m))%43=4 := by
  induction m with
  | zero => decide
  | succ m ih =>
    have he : 3^(6*(m+1)) = 3^(6*m)*729 := by
      rw [show 6*(m+1)=6*m+6 by omega, Nat.pow_add]
    calc
      (4:Nat)^(3^(6*(m+1)))%43 = (4^(3^(6*m)))^729%43 := by rw [he,Nat.pow_mul]
      _ = ((4^(3^(6*m))%43)^729)%43 := by rw [Nat.pow_mod]
      _ = 4 := by rw [ih, pow4_729]

private theorem two_target (m : Nat) : (2:Nat)^(2*3^(6*m))%43=4 := by
  rw [Nat.pow_mul]
  exact four_six m

private theorem ratio21 (t : Nat) : (2:Nat)^(21*(t+1))%43 = (3:Nat)^(21*(t+1))%43 := by
  have he2 : (2:Nat)^21%43=42 := by decide
  have he3 : (3:Nat)^21%43=42 := by decide
  simp only [Nat.pow_mul, Nat.pow_mod, he2, he3]

private theorem two_three_mod (t : Nat) : (2:Nat)^(21*t+21)%43 = (3:Nat)^(21*t+21)%43 := by
  have he : 21*t+21=21*(t+1) := by omega
  rw [he]
  exact ratio21 t

theorem mod43_sufficient (m t q : Nat)
    (hq : 3^(21*t+20)*q+1=2^(2*3^(6*m))) :
    ((2:Nat)^(21*t+21)*q)%43=9 := by
  have hm := congrArg (fun x : Nat => x%43) hq
  rw [Nat.add_mod,two_target] at hm
  have h3q : (3^(21*t+20)*q)%43=3 := by omega
  have he := two_three_mod t
  have hfactor : (3:Nat)^(21*t+21) = 3*3^(21*t+20) := by
    rw [show 21*t+21=21*t+20+1 by omega,Nat.pow_succ]
    ac_rfl
  calc
    ((2:Nat)^(21*t+21)*q)%43 = ((2^(21*t+21)%43)*(q%43))%43 := by rw [Nat.mul_mod]
    _ = ((3^(21*t+21)%43)*(q%43))%43 := by rw [he]
    _ = (3^(21*t+21)*q)%43 := (Nat.mul_mod (3^(21*t+21)) q 43).symm
    _ = (3*(3^(21*t+20)*q))%43 := by rw [hfactor, Nat.mul_assoc]
    _ = 9 := by rw [Nat.mul_mod, h3q]

-- Additional a=6 generic parents with the exact required parity and size.
theorem parent_arithmetic (h q : Nat) (hh : 20 ≤ h) (hq : 7 ≤ q)
    (hq3 : q%3=0) (hm43 : ((2:Nat)^(h+1)*q)%43=9) :
    ∃ v : Nat, 5 ≤ v ∧ v%2=1 ∧ 129*v+9=2^(h+1)*q := by
  let P := 2^(h+1)*q
  have hpow : 2048 ≤ 2^(h+1) := by
    have hp := Nat.pow_le_pow_right (n:=2) (by decide) (show 11 ≤ h+1 by omega)
    simpa using hp
  have hprod : 14336 ≤ P := by
    dsimp [P]
    have := Nat.mul_le_mul hpow hq
    omega
  have heven : P%2=0 := by
    dsimp [P]
    rw [Nat.mul_mod, Nat.pow_succ, Nat.mul_mod]
    simp
  have hp3 : P%3=0 := by
    dsimp [P]
    rw [Nat.mul_mod, hq3]
    simp
  have hp129 : P%129=9 := by
    have hm : P%43=9 := hm43
    omega
  have hdec : P%129+129*(P/129)=P := Nat.mod_add_div P 129
  refine ⟨P/129, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega

theorem parent_six (m t q : Nat)
    (hq : 3^(21*t+20)*q+1=2^(2*3^(6*m))) (hmin : 7≤q) (hq3 : q%3=0) :
    ∃ v : Nat, 5≤v ∧ v%2=1 ∧ 129*v+9=2^(21*t+21)*q := by
  have hm := mod43_sufficient m t q hq
  exact parent_arithmetic (21*t+20) q (by omega) hmin hq3 hm

#print axioms mod43_sufficient
#print axioms parent_arithmetic
#print axioms parent_six
end SheepA6Boost
