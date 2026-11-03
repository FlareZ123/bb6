import Agent30GeneralFiniteFactor

namespace BB6.Agent30GeneralFactor

theorem iterH_factor_only_gap (r c s k m : Nat)
    (hr : r%2=1) (hgap : r≤2*s) (hm : 0<m)
    (hfactor : ∀ x y : Nat, x%m=y%m →
      (iterH r c s (k+1) x)%m=(iterH r c s (k+1) y)%m) : m ∣ (2*s-r) := by
  let z := iterH r c s k 0
  have hh : (iterH r c s (k+1) (2^k*m))%m =
      (iterH r c s (k+1) 0)%m := by
    apply (hfactor (2^k*m) 0)
    simp
  have hshift : iterH r c s k (2^k*m) = z+r^k*m := by
    simpa [z, Nat.mul_comm] using iterH_two_adic_shift r c s k 0 m
  have hH : (H r c s (z+r^k*m))%m = (H r c s z)%m := by
    change (H r c s (iterH r c s k (2^k*m)))%m =
      (H r c s (iterH r c s k 0))%m at hh
    rwa [hshift] at hh
  have hodd : (r^k)%2=1 := by simp [Nat.pow_mod,hr]
  exact H_odd_multiplier_obstruction r c s z m (r^k) hr hgap hm hodd
    (by simpa only [Nat.mul_comm] using hH)

theorem H_factor_mod_gap (r c s m z : Nat) (hgap:r≤2*s)
    (hm : m ∣ (2*s-r)) : (H r c s z)%m=(s*z+c)%m := by
  have hdelta : r+(2*s-r)=2*s := by omega
  have hz : z=2*(z/2)+z%2 := by omega
  have heq : H r c s z+(2*s-r)*(z/2)=s*z+c := by
    calc
      H r c s z+(2*s-r)*(z/2) = (r+(2*s-r))*(z/2)+s*(z%2)+c := by
        simp only [H,Nat.add_mul]
        ac_rfl
      _ = (2*s)*(z/2)+s*(z%2)+c := by rw [hdelta]
      _ = s*z+c := by
        calc
          (2*s)*(z/2)+s*(z%2)+c = s*(2*(z/2)+z%2)+c := by
            rw [Nat.mul_add]
            ac_rfl
          _ = s*z+c := by rw [←hz]
  have hmultiple : (m ∣ (2*s-r)*(z/2)) := by
    obtain ⟨k,hk⟩ := hm
    refine ⟨k*(z/2), ?_⟩
    rw [hk]
    ac_rfl
  calc
    (H r c s z)%m = (H r c s z+(2*s-r)*(z/2))%m := by
      rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hmultiple]
      simp
    _ = (s*z+c)%m := by rw [heq]

theorem iterH_factor_mod_gap (r c s m n : Nat) (hgap:r≤2*s)
    (hm:m∣2*s-r) :
    ∀ x y : Nat, x%m=y%m → iterH r c s n x%m=iterH r c s n y%m := by
  induction n with
  | zero => intro x y hxy; exact hxy
  | succ n ih =>
    intro x y hxy
    change H r c s (iterH r c s n x)%m = H r c s (iterH r c s n y)%m
    rw [H_factor_mod_gap _ _ _ m _ hgap hm, H_factor_mod_gap _ _ _ m _ hgap hm]
    have hh := ih x y hxy
    rw [Nat.add_mod (s*iterH r c s n x) c m,
        Nat.add_mod (s*iterH r c s n y) c m,
        Nat.mul_mod s (iterH r c s n x) m,
        Nat.mul_mod s (iterH r c s n y) m,
        hh]

/-- Complete finite congruence quotient classification for all positive iterates. -/
theorem iterH_factor_iff_gap (r c s n m : Nat) (hr:r%2=1)
    (hgap:r≤2*s) (hn:0<n) (hm:0<m) :
    (∀ x y : Nat, x%m=y%m → iterH r c s n x%m=iterH r c s n y%m) ↔
    m ∣ (2*s-r) := by
  constructor
  · intro hf
    obtain ⟨k,rfl⟩ : ∃ k, n=k+1 := ⟨n-1, by omega⟩
    exact iterH_factor_only_gap r c s k m hr hgap hm hf
  · intro hd
    exact iterH_factor_mod_gap r c s m n hgap hd

#print axioms iterH_factor_iff_gap
#print axioms iterH_factor_only_gap
#print axioms H_odd_multiplier_obstruction
#print axioms H_factor_mod_gap
end BB6.Agent30GeneralFactor
