import Std
import SheepChain2

namespace SheepInteriorGate

/-- An interior node of a distinguished Sheep P-chain has x+12
    divisible by nine whenever its terminal node has one further
    P-predecessor available. -/
theorem interior_nine {n x y : Nat} (c : SheepChain2.Chain2 n x y)
    (h : 9^(n+1) ∣ y+12) : 9 ∣ x+12 := by
  obtain ⟨m, hm⟩ := h
  have hchain := SheepChain2.chain_offset c
  have he : 9^n * (x+12) = 9^n * (8^n*9*m) := by
    calc
      9^n * (x+12) = 8^n * (y+12) := hchain
      _ = 8^n * (9^(n+1)*m) := by rw [hm]
      _ = 9^n * (8^n*9*m) := by
        rw [Nat.pow_succ]
        ac_rfl
  have hpos : 0<9^n := Nat.pow_pos (by decide : 0<9)
  have hx : x+12=8^n*9*m := Nat.eq_of_mul_eq_mul_left hpos he
  refine ⟨8^n*m, ?_⟩
  rw [hx]
  ac_rfl

/-- At any interior P-chain node, the hidden odd-return length h in
    a genuine Sheep E predecessor must be zero. -/
theorem interior_hidden_zero {n x y h u : Nat}
    (c : SheepChain2.Chain2 n x y)
    (hd : 9^(n+1) ∣ y+12)
    (hshape : x = 1+3^h*u) : h=0 := by
  have hn : 9 ∣ x+12 := interior_nine c hd
  have hx3 : (x+12)%3=0 := by
    obtain ⟨z, hz⟩ := hn
    have hh : 3 ∣ x+12 := ⟨3*z, by omega⟩
    exact Nat.mod_eq_zero_of_dvd hh
  by_cases hh : h=0
  · exact hh
  have hhpos : 1≤h := by omega
  obtain ⟨t, rfl⟩ : ∃ t, h=t+1 := ⟨h-1, by omega⟩
  have hv3 : 3 ∣ 3^(t+1)*u := by
    refine ⟨3^t*u, ?_⟩
    rw [Nat.pow_succ]
    ac_rfl
  have hy3 : (3^(t+1)*u)%3=0 := Nat.mod_eq_zero_of_dvd hv3
  omega

private theorem period2_mod3 (n : Nat) : 2^(2*n)%3=1 := by
  induction n with
  | zero => decide
  | succ n ih =>
      have hh : 2^(2*(n+1))=2^(2*n)*4 := by
        rw [show 2*(n+1)=2*n+2 by omega, Nat.pow_add]
      rw [hh, Nat.mul_mod, ih]

/-- At any interior P-chain node, an incoming generic h=0 edge
    with even valuation a must have a≡2 mod3. Hence valuations 6s and
    6s+4 are *impossible at every interior depth* for all eight families. -/
theorem interior_even_a_mod3 {n x y a v : Nat}
    (c : SheepChain2.Chain2 n x y)
    (hd : 9^(n+1) ∣ y+12)
    (hgen : 2*x+1=(2^(a+1)+1)*v+2*a)
    (ha : a%2=0) : a%3=2 := by
  have hn : 9 ∣ x+12 := interior_nine c hd
  have hx3 : (x+12)%3=0 := by
    obtain ⟨z, hz⟩ := hn
    have hh : 3 ∣ x+12 := ⟨3*z, by omega⟩
    exact Nat.mod_eq_zero_of_dvd hh
  have hx : x%3=0 := by omega
  have hrepr : a=2*(a/2) := by omega
  have hp : 2^(a+1)%3=2 := by
    have hh : a+1=2*(a/2)+1 := by omega
    rw [hh, Nat.pow_succ, Nat.mul_mod, period2_mod3]
  have hpow : (2^(a+1)+1)%3=0 := by omega
  have hzero : (((2^(a+1)+1)*v)%3)=0 := by
    rw [Nat.mul_mod, hpow]
    simp
  omega

/-- A genuine h=0 odd-cofactor-three predecessor can enter such an
    interior node only at a valuation divisible by three. -/
theorem interior_special_a_mod3 {n x y a : Nat}
    (c : SheepChain2.Chain2 n x y)
    (hd : 9^(n+1) ∣ y+12)
    (hspecial : x=3*2^a+a+3) : a%3=0 := by
  have hn : 9 ∣ x+12 := interior_nine c hd
  obtain ⟨z, hz⟩ := hn
  omega

/-- Any cofactor-three section predecessor of a source with valuation exactly
    two (the ordinary P-corridor shape) must have a≡1 mod8. -/
theorem special_val8 {x a : Nat}
    (hx : x%8=4)
    (hs : x=3*2^a+a+3) : a%8=1 := by
  have ha3 : 3≤a := by
    by_cases hh : 3≤a
    · exact hh
    have hc : a=0 ∨ a=1 ∨ a=2 := by omega
    rcases hc with h0 | h1 | h2
    · subst a
      simp at hs
      omega
    · subst a
      simp at hs
      omega
    · subst a
      simp at hs
      omega
  have he : a=3+(a-3) := by omega
  have hpow : 2^a = 8*2^(a-3) := by
    calc
      2^a = 2^(3+(a-3)) := by rw [←he]
      _ = 8*2^(a-3) := by simp [Nat.pow_add]
  have hmod : (3*2^a)%8=0 := by
    rw [hpow, Nat.mul_mod]
    simp
  omega

/-- Complete special-source necessary valuation class at interior P nodes. -/
theorem interior_special_val24 {n x y a : Nat}
    (c : SheepChain2.Chain2 n x y)
    (hd : 9^(n+1) ∣ y+12)
    (hx : x%8=4)
    (hspecial : x=3*2^a+a+3) : a%24=9 := by
  have h3 : a%3=0 := interior_special_a_mod3 c hd hspecial
  have h8 : a%8=1 := special_val8 hx hspecial
  omega

#print axioms special_val8
#print axioms interior_special_val24

#print axioms interior_even_a_mod3
#print axioms interior_special_a_mod3
#print axioms interior_nine
#print axioms interior_hidden_zero
end SheepInteriorGate
