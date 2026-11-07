import Lean.Elab.Tactic.Omega

namespace BB6Modular

private theorem two_mod_cases (m x y : Nat) (_hm : 0<m)
    (hx : x<2*m) (hy : y<2*m) (h : x%m=y%m) :
    x=y ∨ (x+m)%(2*m)=y := by
  by_cases hl : x<m
  · have hmx : x%m=x := Nat.mod_eq_of_lt hl
    by_cases hr : y<m
    · have hmy : y%m=y := Nat.mod_eq_of_lt hr
      left; omega
    · have hmy : y%m=y-m := by
        rw [Nat.mod_eq_sub_mod (by omega : m≤y)]
        exact Nat.mod_eq_of_lt (by omega)
      right
      rw [Nat.mod_eq_of_lt (by omega : x+m<2*m)]
      omega
  · have hmx : x%m=x-m := by
      rw [Nat.mod_eq_sub_mod (by omega : m≤x)]
      exact Nat.mod_eq_of_lt (by omega)
    by_cases hr : y<m
    · have hmy : y%m=y := Nat.mod_eq_of_lt hr
      right
      rw [Nat.mod_eq_sub_mod (by omega : 2*m≤x+m)]
      rw [Nat.mod_eq_of_lt (by omega : x+m-2*m<2*m)]
      omega
    · have hmy : y%m=y-m := by
        rw [Nat.mod_eq_sub_mod (by omega : m≤y)]
        exact Nat.mod_eq_of_lt (by omega)
      left; omega

private theorem odd_shift (m d t : Nat) (_hm : 0<m) (hd : d%2=1) :
    (d*(t+m))%(2*m) = (d*t+m)%(2*m) := by
  have hodd : d=2*(d/2)+1 := by omega
  have he : d*m = m + (2*m)*(d/2) := by
    calc
      d*m = (2*(d/2)+1)*m := congrArg (· * m) hodd
      _ = m + (2*m)*(d/2) := by grind +ring
  rw [Nat.mul_add, he]
  calc
    (d*t+(m+(2*m)*(d/2)))%(2*m) =
        (d*t+m+(2*m)*(d/2))%(2*m) := by simp [Nat.add_assoc]
    _ = (d*t+m)%(2*m) := by simp

/-- Elementary constructive surjectivity of multiplication by an odd
    natural number modulo any power of two. No Euler/Fermat prerequisites. -/
theorem odd_mul_surjective (d E r : Nat) (hd : d%2=1) :
    ∃ t, (d*t) % (2^E) = r % (2^E) := by
  induction E with
  | zero => exact ⟨0, by simp [Nat.mod_one]⟩
  | succ E ih =>
      obtain ⟨t,ht⟩ := ih
      let m := 2^E
      have hm : 0<m := Nat.pow_pos (by decide)
      have hM : 2*m = 2^(E+1) := by
        dsimp [m]
        simp [Nat.pow_succ, Nat.mul_comm]
      have hx : (d*t)%(2*m)<2*m := Nat.mod_lt _ (by omega)
      have hy : r%(2*m)<2*m := Nat.mod_lt _ (by omega)
      have hmod : ((d*t)%(2*m))%m=(r%(2*m))%m := by
        have h1 : ((d*t)%(2*m))%m=(d*t)%m := by
          rw [Nat.mod_mul_left_mod]
        have h2 : (r%(2*m))%m=r%m := by
          rw [Nat.mod_mul_left_mod]
        simpa only [h1,h2,m] using ht
      rcases two_mod_cases m ((d*t)%(2*m)) (r%(2*m)) hm hx hy hmod with heq | heq
      · exact ⟨t, by simpa only [hM] using heq⟩
      · refine ⟨t+m, ?_⟩
        have hs := odd_shift m d t hm hd
        have hres : (d*(t+m))%(2*m) = r%(2*m) := by
          rw [hs]
          calc
            (d*t+m)%(2*m) = ((d*t)%(2*m)+m)%(2*m) :=
              (Nat.mod_add_mod _ _ _).symm
            _ = r%(2*m) := heq
        simpa only [hM] using hres

#print axioms odd_mul_surjective
end BB6Modular
