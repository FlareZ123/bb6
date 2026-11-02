import BConstantCore
namespace BB6.OneDim

/-- Constant parity blocks correspond precisely to dyadic divisibility of the
    branch-specific 2-adic fixed point displacement. -/
theorem constant_prefix_iff_divides (bit n z : Nat) (hb : bit ≤ 1) :
    samePrefix bit n z ↔ 2^n ∣ z+(if bit=0 then 8 else 15) := by
  let c := if bit=0 then 8 else 15
  change samePrefix bit n z ↔ 2^n ∣ z+c
  induction n generalizing z with
  | zero => simp [samePrefix]
  | succ n ih =>
      simp only [samePrefix]
      constructor
      · rintro ⟨hz, hr⟩
        obtain ⟨w,hw⟩ := (ih (G z)).mp hr
        have bal : 2*(G z+c)=3*(z+c) := G_balance_bit bit z hb hz
        have hd : 2^(n+1) ∣ 3*(z+c) := by
          refine ⟨w, ?_⟩
          calc
            3*(z+c) = 2*(G z+c) := bal.symm
            _ = 2*(2^n*w) := by rw [hw]
            _ = 2^(n+1)*w := by simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        have cop : Nat.Coprime (2^(n+1)) 3 :=
          Nat.Coprime.pow_left (n+1) (by decide)
        exact cop.dvd_of_dvd_mul_left hd
      · intro hd
        obtain ⟨w,hw⟩ := hd
        have hz : z%2=bit := by
          have hres : z+c = 2*(2^n*w) := by
            calc
              z+c = 2^(n+1)*w := hw
              _ = 2*(2^n*w) := by simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          have hcase : bit=0 ∨ bit=1 := by omega
          rcases hcase with h | h
          · subst bit
            dsimp [c] at hres
            omega
          · subst bit
            dsimp [c] at hres
            omega
        refine ⟨hz, (ih (G z)).mpr ?_⟩
        have bal : 2*(G z+c)=3*(z+c) := G_balance_bit bit z hb hz
        have heq : G z+c = 2^n*(3*w) := by
          have hmul : 2*(G z+c)=2*(2^n*(3*w)) := by
            calc
              2*(G z+c) = 3*(z+c) := bal
              _ = 3*(2^(n+1)*w) := by rw [hw]
              _ = 2*(2^n*(3*w)) := by simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          omega
        exact ⟨3*w,heq⟩

theorem scalar_constant_run (bit n z : Nat) (hb : bit≤1) :
    (∀ i : Nat, i<n → (iterG i z)%2=bit) ↔
      2^n ∣ z+(if bit=0 then 8 else 15) := by
  exact (samePrefix_iff bit n z).symm.trans (constant_prefix_iff_divides bit n z hb)

#print axioms scalar_constant_run
end BB6.OneDim
