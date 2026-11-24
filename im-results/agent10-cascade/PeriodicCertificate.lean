import Std

namespace CascadePeriodCertificate

/-- Numerator of an exponential-affine phase sampled at period boundaries.
    The starting power of two and constant level offset are absorbed in A,C. -/
def phase (A B C G : Int) (j : Nat) : Int := A*G^j+B*(j:Int)+C

/-- The characteristic polynomial is (T-G)(T-1)^2. -/
theorem phase_recurrence (A B C G : Int) (j : Nat) :
    phase A B C G (j+3) = (G+2)*phase A B C G (j+2) -
      (2*G+1)*phase A B C G (j+1) + G*phase A B C G j := by
  unfold phase
  simp only [Int.pow_succ, Int.natCast_succ]
  grind

/-- Any congruence verified at the first three samples holds forever.
    For odd integrality of X=N/Q, choose modulus 2Q and residue Q. -/
theorem three_congruences_all (A B C G M R : Int)
    (h0 : M ∣ phase A B C G 0-R)
    (h1 : M ∣ phase A B C G 1-R)
    (h2 : M ∣ phase A B C G 2-R) :
    ∀ j : Nat, M ∣ phase A B C G j-R := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    by_cases hj : j<3
    · have h : j=0 ∨ j=1 ∨ j=2 := by omega
      rcases h with h|h|h <;> subst j <;> assumption
    · let k := j-3
      have hk : j=k+3 := by omega
      obtain ⟨u,hu⟩ := ih k (by omega)
      obtain ⟨v,hv⟩ := ih (k+1) (by omega)
      obtain ⟨w,hw⟩ := ih (k+2) (by omega)
      refine ⟨(G+2)*w-(2*G+1)*v+G*u,?_⟩
      rw [hk,phase_recurrence]
      grind

/-- The second difference determines the exponential coefficient obstruction. -/
theorem second_difference (A B C G : Int) (j : Nat) :
    phase A B C G (j+2)-2*phase A B C G (j+1)+phase A B C G j =
      A*G^j*(G-1)^2 := by
  unfold phase
  simp only [Int.pow_succ, Int.natCast_succ]
  grind

#print axioms phase_recurrence
#print axioms three_congruences_all
#print axioms second_difference
end CascadePeriodCertificate
