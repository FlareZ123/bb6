import Std
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
namespace SheepA7Boost

private theorem four_nine (s : Nat) : (4:Nat)^(9^s)%257=4 := by
  induction s with
  | zero => decide
  | succ s ih =>
    calc
      (4:Nat)^(9^(s+1)) %257 = ((4:Nat)^(9^s))^9 %257 := by
        rw [Nat.pow_succ,Nat.pow_mul]
      _ = ((4^(9^s)%257)^9)%257 := by rw [Nat.pow_mod]
      _ = 4 := by rw [ih]

private theorem four_three_nine (s : Nat) : (4:Nat)^(3*9^s)%257=64 := by
  calc
    (4:Nat)^(3*9^s)%257 = ((4:Nat)^(9^s))^3%257 := by rw [Nat.mul_comm,Nat.pow_mul]
    _ = ((4^(9^s)%257)^3)%257 := by rw [Nat.pow_mod]
    _ = 64 := by rw [four_nine]

private theorem even_target (s : Nat) : (2:Nat)^(2*9^s)%257=4 := by
  rw [Nat.pow_mul]
  exact four_nine s

private theorem odd_target (s : Nat) : (2:Nat)^(2*(3*9^s))%257=64 := by
  rw [Nat.pow_mul]
  exact four_three_nine s

private theorem modular_exponents (a e p : Nat) (ha : a^p%257=1) :
    a^(p*e)%257=1 := by
  rw [Nat.pow_mul,Nat.pow_mod,ha]
  simp

private theorem exp_even2 (t : Nat) : (2:Nat)^(256*t+222)%257=193 := by
  rw [Nat.pow_add,Nat.mul_mod,modular_exponents 2 t 256 (by decide)]

private theorem exp_even3 (t : Nat) : (3:Nat)^(256*t+221)%257=76 := by
  rw [Nat.pow_add,Nat.mul_mod,modular_exponents 3 t 256 (by decide)]

private theorem exp_odd2 (t : Nat) : (2:Nat)^(256*t+84)%257=16 := by
  rw [Nat.pow_add,Nat.mul_mod,modular_exponents 2 t 256 (by decide)]

private theorem exp_odd3 (t : Nat) : (3:Nat)^(256*t+83)%257=115 := by
  rw [Nat.pow_add,Nat.mul_mod,modular_exponents 3 t 256 (by decide)]

theorem mod_even (s t q : Nat)
    (hq : 3^(256*t+221)*q+1 = 2^(2*9^s)) :
    ((2:Nat)^(256*t+222)*q)%257=11 := by
  have hm := congrArg (fun x : Nat => x%257) hq
  rw [Nat.add_mod,Nat.mul_mod,exp_even3,even_target] at hm
  have hqmod : q%257=44 := by
    have all : ∀ z : Fin 257,
      ((76*z.val)%257+1)%257=4 → z.val=44 := by decide
    exact all ⟨q%257,Nat.mod_lt q (by decide)⟩ hm
  rw [Nat.mul_mod,exp_even2,hqmod]

theorem mod_odd (s t q : Nat)
    (hq : 3^(256*t+83)*q+1 = 2^(2*(3*9^s))) :
    ((2:Nat)^(256*t+84)*q)%257=11 := by
  have hm := congrArg (fun x : Nat => x%257) hq
  rw [Nat.add_mod,Nat.mul_mod,exp_odd3,odd_target] at hm
  have hqmod : q%257=81 := by
    have all : ∀ z : Fin 257,
      ((115*z.val)%257+1)%257=64 → z.val=81 := by decide
    exact all ⟨q%257,Nat.mod_lt q (by decide)⟩ hm
  rw [Nat.mul_mod,exp_odd2,hqmod]

theorem parent_arithmetic (h q : Nat) (hh : 10 ≤ h) (hq : 7≤q)
    (hm : ((2:Nat)^(h+1)*q)%257=11) :
    ∃ v : Nat, 5 ≤ v ∧ v%2=1 ∧ 257*v+11=2^(h+1)*q := by
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
    rw [Nat.mul_mod,Nat.pow_succ,Nat.mul_mod]
    simp
  have hdec : P%257+257*(P/257)=P := Nat.mod_add_div P 257
  refine ⟨P/257, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega

theorem parent_even (s t q : Nat)
    (hq : 3^(256*t+221)*q+1=2^(2*9^s)) (hmin : 7≤q) :
    ∃ v : Nat, 5≤v ∧ v%2=1 ∧ 257*v+11=2^(256*t+222)*q := by
  exact parent_arithmetic (256*t+221) q (by omega) hmin (mod_even s t q hq)

theorem parent_odd (s t q : Nat)
    (hq : 3^(256*t+83)*q+1=2^(2*(3*9^s))) (hmin : 7≤q) :
    ∃ v : Nat, 5≤v ∧ v%2=1 ∧ 257*v+11=2^(256*t+84)*q := by
  exact parent_arithmetic (256*t+83) q (by omega) hmin (mod_odd s t q hq)

#print axioms mod_even
#print axioms mod_odd
#print axioms parent_arithmetic
#print axioms parent_even
#print axioms parent_odd
end SheepA7Boost
