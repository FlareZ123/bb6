import AffineNormalize
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11ThreeAffine

/-- The whole complementary odd-part-three dyadic cone avoids the
    terminal affine-normalized right-four obstruction. This is
    an exact original-source algebraic property, any inverse depth. -/
theorem dyadic_three_affine_right_ne_four (r a b u : Nat)
    (hu : 7≤u) (hu4 : u%4=3)
    (hb : b+2=2^r*u)
    (hmass : (a+2*b+4*r)%8=3) :
    (BB6.Agent15.affineNormalize a b).2≠4 := by
  induction r generalizing a b with
  | zero =>
      have hbodd : b%2=1 := by simp at hb; omega
      have hguard : ¬(4≤b ∧ b%2=0 ∧ (a+b)%4=1) := by omega
      rw [BB6.Agent15.affineNormalize, dif_neg hguard]
      omega
  | succ s ih =>
      by_cases hs : s=0
      · subst s
        have hb2 : b+2=2*u := by simpa using hb
        have hb4 : b%4=0 := by omega
        have ha4 : a%4=3 := by
          have hm : (a+2*b+4)%8=3 := by simpa using hmass
          omega
        have hguard : ¬(4≤b ∧ b%2=0 ∧ (a+b)%4=1) := by omega
        rw [BB6.Agent15.affineNormalize, dif_neg hguard]
        omega
      · have hr2 : 2≤s+1 := by omega
        have hpow : (2:Nat)^2∣2^(s+1) := Nat.pow_dvd_pow 2 (by omega)
        have h4 : 4∣2^(s+1) := by simpa using hpow
        have hb4 : b%4=2 := by
          rcases h4 with ⟨v,hv⟩
          have he : 4∣b+2 := by
            refine ⟨v*u,?_⟩
            rw [hb,hv]
            simp only [Nat.mul_assoc]
          omega
        have ha4 : a%4=3 := by omega
        have hguard : 4≤b ∧ b%2=0 ∧ (a+b)%4=1 := by
          have hp : 1≤2^(s+1) := Nat.pow_pos (by decide)
          have hmul : u≤2^(s+1)*u := by
            simpa using Nat.mul_le_mul_right u hp
          omega
        have hbnext : ((b-2)/2)+2=2^s*u := by
          have hh : b+2=2*(2^s*u) := by
            calc
              b+2=2^(s+1)*u := hb
              _=2*(2^s*u) := by rw [Nat.pow_succ]; ac_rfl
          omega
        have hmnext : ((a+b-2)+2*((b-2)/2)+4*s)%8=3 := by omega
        rw [BB6.Agent15.affineNormalize, dif_pos hguard]
        exact ih (a+b-2) ((b-2)/2) hbnext hmnext

#print axioms dyadic_three_affine_right_ne_four
end BB6.Agent11ThreeAffine
