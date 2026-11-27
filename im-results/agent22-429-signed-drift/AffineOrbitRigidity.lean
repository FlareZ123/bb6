import Std

namespace PeriodicRigidity

/-- An infinite sequence of naturals that shrinks by a factor at least 2
    each time is identically zero. -/
theorem no_nat_scaled (M : Nat) (hM : 2 ≤ M)
  (f : Nat → Nat) (h : ∀ n, f n = M * f (n+1)) :
  ∀ n, f n = 0 := by
  intro n
  by_cases hn : f n = 0
  · exact hn
  · exfalso
    have hbwd (j : Nat) : f (n+j) = 0 → f n = 0 := by
      induction j with
      | zero => simpa
      | succ j ih =>
        intro hz
        apply ih
        have hs := h (n+j)
        have heq : n+j+1=n+(j+1) := by omega
        rw [heq, hz] at hs
        simpa using hs
    have hpos (j : Nat) : 0 < f (n+j) := by
      have hne : f (n+j) ≠ 0 := by
        intro he
        exact hn (hbwd j he)
      omega
    have hdec (j : Nat) : f (n+j+1) + 1 ≤ f (n+j) := by
      have hh := h (n+j)
      have hp := hpos (j+1)
      have hj : n+j+1=n+(j+1) := by omega
      rw [hj] at hh
      rw [hj]
      have hmul : 2 * f (n+(j+1)) ≤ M * f (n+(j+1)) :=
        Nat.mul_le_mul_right (f (n+(j+1))) hM
      omega
    have hbound (j : Nat) : f (n+j)+j ≤ f n := by
      induction j with
      | zero => simp
      | succ j ih =>
        have hs := hdec j
        have heq : n+j+1=n+(j+1) := by omega
        rw [heq] at hs
        omega
    have hi := hbound (f n+1)
    omega

theorem no_int_scaled (M : Nat) (hM : 2 ≤ M)
  (w : Nat → Int) (hw : ∀ n, w n = (M:Int) * w (n+1)) :
  ∀ n, w n = 0 := by
  let f : Nat → Nat := fun n => (w n).natAbs
  have hf (n : Nat) : f n = M * f (n+1) := by
    dsimp [f]
    rw [hw n, Int.natAbs_mul, Int.natAbs_natCast]
  have hz := no_nat_scaled M hM f hf
  intro n
  exact Int.natAbs_eq_zero.mp (hz n)

theorem affine_difference_rigidity (M : Nat) (hM : 2 ≤ M)
  (d : Nat → Int) (p : Int)
  (hd : ∀ n, (M:Int) * d (n+1) = d n + p) :
  ∀ n, ((M:Int)-1) * d n = p := by
  let w : Nat → Int := fun n => ((M:Int)-1) * d n - p
  have hw (n : Nat) : w n = (M:Int) * w (n+1) := by
    dsimp [w]
    have heq := hd n
    grind
  have hz := no_int_scaled M hM w hw
  intro n
  have hn := hz n
  dsimp [w] at hn
  omega

/-- Exact integral-affine rigidity for a contracting, linearly forced
    recurrence. Unlike an analytical limit argument this proof is
    constructive and purely discrete. -/
theorem affine_orbit_rigidity (M : Nat) (hM : 2 ≤ M)
    (u : Nat → Int) (p q : Int)
    (hu : ∀ n, (M:Int) * u (n+1) = u n + p * (n:Int) + q) :
    ∃ s b : Int, (∀ n, u n = s * (n:Int) + b) ∧ ((M:Int)-1)*s = p := by
  let d : Nat → Int := fun n => u (n+1) - u n
  have hd (n : Nat) : (M:Int) * d (n+1) = d n + p := by
    dsimp [d]
    have h0 := hu n
    have h1 := hu (n+1)
    grind
  have hfixed := affine_difference_rigidity M hM d p hd
  let s := d 0
  let b := u 0
  have hslope : ∀ n, d n = s := by
    intro n
    have hn := hfixed n
    have hMne : (M:Int) - 1 ≠ 0 := by omega
    have hmul : ((M:Int)-1)*d n = ((M:Int)-1)*s := by
      simpa only [s] using (hfixed n).trans (hfixed 0).symm
    exact Int.eq_of_mul_eq_mul_left hMne hmul
  have hline : ∀ n, u n = s * (n:Int) + b := by
    intro n
    induction n with
    | zero => simp [b]
    | succ n ih =>
      have he := hslope n
      dsimp [d] at he
      grind
  exact ⟨s, b, hline, hfixed 0⟩

#print axioms PeriodicRigidity.no_nat_scaled
#print axioms PeriodicRigidity.no_int_scaled
#print axioms PeriodicRigidity.affine_difference_rigidity
#print axioms PeriodicRigidity.affine_orbit_rigidity
end PeriodicRigidity
