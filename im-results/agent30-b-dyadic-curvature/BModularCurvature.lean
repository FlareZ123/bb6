import Agent10Shift

namespace BB6.Agent30B
open BB6.Agent10B

theorem G_odd_scale_curvature (y s : Nat) (hs : s % 2 = 1) :
  (y % 2 = 0 ∧ G y + G (y+2*s)+7=2*G (y+s)) ∨
  (y % 2 = 1 ∧ G y + G (y+2*s)=2*G (y+s)+7) := by
  by_cases hp : y % 2 = 0
  · left
    constructor
    · exact hp
    · simp only [G]
      omega
  · right
    constructor
    · omega
    · simp only [G]
      omega

theorem iterG_succ_last (n z : Nat) :
    iterG (n+1) z = G (iterG n z) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    change iterG (n+1) (G z)=G (iterG (n+1) z)
    exact ih (G z)

/-- Every positive iterate of the scalar B map has a seven-unit
    second difference on the dyadic scale 2^(n-1). -/
theorem iterG_dyadic_curvature (n z : Nat) :
    (iterG (n+1) z + iterG (n+1) (z+2*2^n)+7 =
       2*iterG (n+1) (z+2^n)) ∨
    (iterG (n+1) z + iterG (n+1) (z+2*2^n) =
       2*iterG (n+1) (z+2^n)+7) := by
  have h1 : iterG n (z+2^n)=iterG n z+3^n := by
    simpa using (G_iter_two_adic_shift n z 1)
  have h2 : iterG n (z+2*2^n)=iterG n z+2*3^n := by
    simpa [Nat.mul_comm] using (G_iter_two_adic_shift n z 2)
  have hodd : (3^n)%2=1 := by simp [Nat.pow_mod]
  have hcurv := G_odd_scale_curvature (iterG n z) (3^n) hodd
  simp only [iterG_succ_last]
  rw [h1,h2]
  rcases hcurv with ⟨_,hc⟩ | ⟨_,hc⟩
  · exact Or.inl hc
  · exact Or.inr hc

private theorem affine_second_mod (m a b x t : Nat) (f : Nat → Nat)
    (h : ∀ z, f z % m = (a*z+b)%m) :
    (f x + f (x+2*t)) % m = (2*f (x+t)) % m := by
  have hlinear : a*x+b + (a*(x+2*t)+b) =
      2*(a*(x+t)+b) := by
    have htwice : a*(2*t)=2*(a*t) := by ac_rfl
    rw [Nat.mul_add a x (2*t), htwice]
    simp [Nat.mul_add]
    omega
  calc
    (f x + f (x+2*t)) % m =
        (f x % m + f (x+2*t)%m)%m := Nat.add_mod _ _ _
    _ = ((a*x+b)%m + (a*(x+2*t)+b)%m)%m := by
      rw [h x,h (x+2*t)]
    _ = (a*x+b + (a*(x+2*t)+b))%m :=
      (Nat.add_mod _ _ _).symm
    _ = (2*(a*(x+t)+b))%m := by rw [hlinear]
    _ = (2%m * ((a*(x+t)+b)%m))%m := Nat.mul_mod _ _ _
    _ = (2%m * (f (x+t)%m))%m := by rw [h (x+t)]
    _ = (2*f (x+t))%m := (Nat.mul_mod _ _ _).symm

private theorem mod_eq_gap_dvd (m u v d : Nat)
    (h : u%m=v%m) (heq : u+d=v) : m∣d := by
  obtain ⟨k1,k2,hk⟩ := Nat.mod_eq_mod_iff.mp h
  have hd1 : m∣k1*m := ⟨k1, by simp [Nat.mul_comm]⟩
  have hd2 : m∣k2*m := ⟨k2, by simp [Nat.mul_comm]⟩
  have hs : k1*m-k2*m=d := by omega
  simpa [hs] using Nat.dvd_sub hd1 hd2

/-- If any positive iterate is affine modulo m on all natural inputs,
then the modulus divides seven. Valid for every iteration index and slope. -/
theorem affine_iter_modulus_divides_seven (n m a b : Nat)
    (h : ∀ z, (iterG (n+1) z)%m=(a*z+b)%m) :
    m ∣ 7 := by
  let p := (2:Nat)^n
  let f := iterG (n+1)
  have hmod := affine_second_mod m a b 0 p f h
  have hcurv := iterG_dyadic_curvature n 0
  change (f 0 + f (0+2*p)+7=2*f (0+p)) ∨
    (f 0 + f (0+2*p)=2*f (0+p)+7) at hcurv
  change (f 0 + f (0+2*p))%m = (2*f (0+p))%m at hmod
  rcases hcurv with hc | hc
  · exact mod_eq_gap_dvd m _ _ 7 hmod hc
  · exact mod_eq_gap_dvd m _ _ 7 hmod.symm hc.symm

#print axioms affine_iter_modulus_divides_seven
#print axioms G_odd_scale_curvature
#print axioms iterG_succ_last
#print axioms iterG_dyadic_curvature
end BB6.Agent30B
