import SignedRayPeriod
set_option maxHeartbeats 0
namespace CascadeRayPeriod

private theorem pow_add_two (j:Nat):
    (2:Nat)^(j+2)=4*2^j := by
  rw [Nat.pow_add]
  rw [show (2:Nat)^2 = 4 by decide]
  omega

private theorem pow_add_three (j:Nat):
    (2:Nat)^(j+3)=8*2^j := by
  rw [Nat.pow_add]
  rw [show (2:Nat)^3 = 8 by decide]
  omega

/-- Every second inverse ray numerator decreases by precisely a multiple of six. -/
theorem signedZ_step_two (n j:Nat) :
    signedZ n (j+2) = signedZ n j - 6*(2:Int)^j*(2*n+3) := by
  have hp : (2:Nat)^((j+2)+1) = 8*2^j := by
    rw [show j+2+1=j+3 by omega]
    exact pow_add_three j
  have hq : (2:Nat)^(j+1) = 2*2^j := by
    rw [Nat.pow_succ]; omega
  have hpi : (2:Int)^((j+2)+1) = 8*(2:Int)^j := by exact_mod_cast hp
  have hqi : (2:Int)^(j+1) = 2*(2:Int)^j := by exact_mod_cast hq
  dsimp [signedZ]
  rw [hpi,hqi]
  push_cast
  have hsplit : (8:Int)*(2:Int)^j*(2*(n:Int)+3) =
      2*(2:Int)^j*(2*(n:Int)+3)+6*(2:Int)^j*(2*(n:Int)+3) := by
    rw [show (8:Int)=2+6 by omega, Int.add_mul, Int.add_mul]
  omega

private theorem power_mod_three (j:Nat) :
    (2^j:Nat)%3 = if j%2=0 then 1 else 2 := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih]
    by_cases hj : j%2=0
    · simp [hj]
      omega
    · have hj1:j%2=1:=by omega
      simp [hj1]
      omega

private theorem power_nonzero_three (j:Nat):
    (2^j:Nat)%3=1 ∨ (2^j:Nat)%3=2 := by
  rw [power_mod_three]
  by_cases h : j%2=0
  · simp [h]
  · simp [h]

private theorem sector_pow_mod3 (n:Nat) (hn:n%6=4 ∨ n%6=5):
    (2^n:Nat)%3=n%3 := by
  rw [power_mod_three]
  rcases hn with h|h
  · have hpar:n%2=0:=by omega
    simp [hpar]
    omega
  · have hpar:n%2=1:=by omega
    simp [hpar]
    omega

private theorem signed_even_mod3 (n j:Nat)
    (hn:n%6=4 ∨ n%6=5) (hj:j%2=0):
    signedZ n j%3=0 := by
  have hj1 : (j+1)%2=1 := by omega
  have hpow : (2^(j+1):Nat)%3=2:=by simp [power_mod_three,hj1]
  have hnmatch := sector_pow_mod3 n hn
  have hm : (((2:Nat)^n:Int)%3)=(n:Int)%3 := by exact_mod_cast hnmatch
  have hm2 : (((2:Nat)^(j+1):Int)%3)=2 := by exact_mod_cast hpow
  have hc : ((2*(n:Int)+3)%3)= (2*((n:Int)%3)+3)%3 := by omega
  rcases hn with h|h
  · have hni : (n:Int)%3=1 := by exact_mod_cast (show n%3=1 by omega)
    have hpr : ((((2:Nat)^(j+1):Int)*(2*(n:Int)+3))%3)=1 := by
      rw [Int.mul_emod, hm2, hc, hni]
      decide
    push_cast at hm hm2 hpr
    dsimp [signedZ]
    omega
  · have hni : (n:Int)%3=2 := by exact_mod_cast (show n%3=2 by omega)
    have hpr : ((((2:Nat)^(j+1):Int)*(2*(n:Int)+3))%3)=2 := by
      rw [Int.mul_emod, hm2, hc, hni]
      decide
    push_cast at hm hm2 hpr
    dsimp [signedZ]
    omega

private theorem step_d_nonzero (n j:Nat)
    (hn:n%6=4 ∨ n%6=5) :
    (((2:Int)^j*(2*(n:Int)+3))%3)=1 ∨
    (((2:Int)^j*(2*(n:Int)+3))%3)=2 := by
  have hp_nat := power_nonzero_three j
  have hp : ((2:Int)^j)%3=1 ∨ ((2:Int)^j)%3=2 := by
    rcases hp_nat with h|h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  have hc : (2*(n:Int)+3)%3=1 ∨ (2*(n:Int)+3)%3=2 := by
    rcases hn with h|h
    · right
      have hni : (n:Int)%3=1:=by exact_mod_cast (show n%3=1 by omega)
      omega
    · left
      have hni : (n:Int)%3=2:=by exact_mod_cast (show n%3=2 by omega)
      omega
  have hmul := Int.mul_emod ((2:Int)^j) (2*(n:Int)+3) 3
  rcases hp with hp|hp <;> rcases hc with hc|hc
  all_goals rw [hmul,hp,hc] <;> decide

/-- Arithmetic identities for a whole six-depth inverse packet. -/
theorem signedZ_step_four (n j:Nat) :
    signedZ n (j+4)=signedZ n j-30*(2:Int)^j*(2*n+3) := by
  have hpow : (2:Int)^(j+2)=4*(2:Int)^j := by
    exact_mod_cast pow_add_two j
  have hex : j+4=(j+2)+2:=by omega
  rw [hex, signedZ_step_two, signedZ_step_two, hpow]
  have hmul : 24*(2:Int)^j*(2*(n:Int)+3)=6*(4*(2:Int)^j)*(2*(n:Int)+3) := by
    simp only [← Int.mul_assoc, show (6:Int)*4=24 by decide]
  have hplus : 30*(2:Int)^j*(2*(n:Int)+3) =
      6*(2:Int)^j*(2*(n:Int)+3)+24*(2:Int)^j*(2*(n:Int)+3) := by
    rw [show (30:Int)=6+24 by decide, Int.add_mul, Int.add_mul]
  omega

private theorem elementary_three (z d:Int) (hz:z%3=0)
    (hd:d%3=1 ∨ d%3=2):
    (z%9=0 ∧ (z-6*d)%9=3 ∧ (z-30*d)%9=6) ∨
    (z%9=0 ∧ (z-6*d)%9=6 ∧ (z-30*d)%9=3) ∨
    (z%9=3 ∧ (z-6*d)%9=0 ∧ (z-30*d)%9=6) ∨
    (z%9=3 ∧ (z-6*d)%9=6 ∧ (z-30*d)%9=0) ∨
    (z%9=6 ∧ (z-6*d)%9=0 ∧ (z-30*d)%9=3) ∨
    (z%9=6 ∧ (z-6*d)%9=3 ∧ (z-30*d)%9=0) := by
  rcases hd with hd | hd <;> omega

/-- In every six-level inverse packet starting at even depth, the three
    even-depth signed numerators are exactly 0,3,6 modulo nine in some order. -/
theorem signed_ray_even_packet_permutation (n j:Nat)
    (hn:n%6=4 ∨ n%6=5) (hj:j%2=0):
    (signedZ n j%9=0 ∧ signedZ n (j+2)%9=3 ∧ signedZ n (j+4)%9=6) ∨
    (signedZ n j%9=0 ∧ signedZ n (j+2)%9=6 ∧ signedZ n (j+4)%9=3) ∨
    (signedZ n j%9=3 ∧ signedZ n (j+2)%9=0 ∧ signedZ n (j+4)%9=6) ∨
    (signedZ n j%9=3 ∧ signedZ n (j+2)%9=6 ∧ signedZ n (j+4)%9=0) ∨
    (signedZ n j%9=6 ∧ signedZ n (j+2)%9=0 ∧ signedZ n (j+4)%9=3) ∨
    (signedZ n j%9=6 ∧ signedZ n (j+2)%9=3 ∧ signedZ n (j+4)%9=0) := by
  have hz := signed_even_mod3 n j hn hj
  have hd := step_d_nonzero n j hn
  have h := elementary_three (signedZ n j) ((2:Int)^j*(2*(n:Int)+3)) hz hd
  rw [signedZ_step_two n j, signedZ_step_four n j]
  simpa only [Int.mul_assoc] using h

#print axioms signed_ray_even_packet_permutation
#print axioms signedZ_step_four
#print axioms signedZ_step_two
end CascadeRayPeriod
