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

#print axioms interior_nine
#print axioms interior_hidden_zero
end SheepInteriorGate
