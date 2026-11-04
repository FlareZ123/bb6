import Std
namespace SheepGenericHigh

def Q (D E a : Nat) : Nat := D*(2*a-3)+E

private theorem Q_succ (D E a : Nat) (ha : 2≤a) :
    Q D E (a+1) = Q D E a + 2*D := by
  simp only [Q]
  have hs : 2*(a+1)-3 = (2*a-3)+2 := by omega
  rw [hs, Nat.mul_add]
  omega

/-- One finite base inequality implies the uniform odd 2-adic residue gap,
for every higher valuation; the coefficients are unrestricted naturals. -/
theorem large_odd_gap (D E A : Nat) (hA : 2≤A)
    (hbase : 1<Q D E A ∧ Q D E A%2=1 ∧
      Q D E A < 2^A ∧ 2*D≤2^A) :
    ∀ a : Nat, A≤a →
      1<Q D E a ∧ Q D E a%2=1 ∧ Q D E a<2^a := by
  intro a ha
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le ha
  induction j with
  | zero =>
      simpa using (show 1<Q D E A ∧ Q D E A%2=1 ∧ Q D E A<2^A
        from ⟨hbase.1,hbase.2.1,hbase.2.2.1⟩)
  | succ j ih =>
      have hAi : 2≤A+j := by omega
      have hprev : 1<Q D E (A+j) ∧ Q D E (A+j)%2=1 ∧
          Q D E (A+j)<2^(A+j) := by
        exact ih (by omega)
      have hD : 2*D ≤ 2^(A+j) := by
        have hlow : 2^A ≤ 2^(A+j) :=
          Nat.pow_le_pow_right (by decide) (by omega)
        omega
      have hnext : Q D E (A+(j+1)) = Q D E (A+j)+2*D := by
        rw [show A+(j+1)=(A+j)+1 by omega]
        exact Q_succ D E (A+j) hAi
      have hpow : 2^(A+(j+1)) = 2*2^(A+j) := by
        rw [show A+(j+1)=(A+j)+1 by omega, Nat.pow_succ]
        omega
      rw [hnext, hpow]
      omega

#print axioms large_odd_gap
end SheepGenericHigh
