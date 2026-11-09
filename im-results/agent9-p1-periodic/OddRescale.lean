import OddDifference

namespace BB6.Agent9CrossFeeder

/-- Every prefix of the shared-depth difference recurrence gives arbitrary
2-adic divisibility after subtracting a multiple of the offset. -/
theorem difference_2adic_prefix (C : Int) (D : Nat → Int)
    (t : Nat → Nat)
    (hstep : ∀ n, D n = (2:Int)^(t n)*(2*D (n+1)-C)) :
    ∀ (n k : Nat), ∃ u v : Int, D n = (2:Int)^k*u+C*v := by
  intro n k
  induction k generalizing n with
  | zero =>
      refine ⟨D n,0,?_⟩
      simp
  | succ k ih =>
      obtain ⟨u,v,huv⟩ := ih (n+1)
      refine ⟨(2:Int)^(t n)*u,(2:Int)^(t n)*(2*v-1),?_⟩
      rw [hstep n,huv,Int.pow_succ]
      simp only [Int.mul_add,Int.mul_sub,Int.add_mul,Int.mul_assoc,Int.mul_left_comm,Int.mul_comm, Int.one_mul]
      omega

/-- If the fixed offset is divisible by 2^e, every integer difference in an
infinite shared-depth pair is divisible by 2^e as well. -/
theorem difference_divisible_by_offset_power (e : Nat) (C : Int)
    (D : Nat → Int) (t : Nat → Nat)
    (hC : (2:Int)^e ∣ C)
    (hstep : ∀ n, D n = (2:Int)^(t n)*(2*D (n+1)-C)) :
    ∀ n, (2:Int)^e ∣ D n := by
  intro n
  obtain ⟨u,v,huv⟩ := difference_2adic_prefix C D t hstep n e
  rw [huv]
  exact Int.dvd_add (Int.dvd_mul_right _ _) (Int.dvd_mul_of_dvd_left hC)

/-- Normalizing by the full dyadic factor of the source offset makes the
remaining infinite-depth difference dynamics finite and deterministic. -/
theorem rescaled_odd_difference_has_period (e : Nat) (B : Int)
    (D : Nat → Int) (t : Nat → Nat)
    (hBodd : B%2=1)
    (hstep : ∀ n, D n=(2:Int)^(t n)*(2*D (n+1)-(2:Int)^e*B)) :
    ∃ (N d : Nat) (w : List Nat), 0<d ∧ w.length=d ∧
      ∀ (n k : Nat) (hk : k<w.length),
        t (N+n*d+k) = w.get ⟨k,hk⟩ := by
  let C : Int := (2:Int)^e*B
  have hCdiv : (2:Int)^e ∣ C := Int.dvd_mul_right _ _
  have hd : ∀ n, (2:Int)^e ∣ D n :=
    difference_divisible_by_offset_power e C D t hCdiv hstep
  let E : Nat → Int := fun n => D n / ((2:Int)^e)
  have hEQ : ∀ n, D n=(2:Int)^e*E n := by
    intro n
    exact (Int.mul_ediv_cancel_of_dvd (hd n)).symm
  have hEnext : ∀ n, E n=(2:Int)^(t n)*(2*E (n+1)-B) := by
    intro n
    have hh := hstep n
    rw [hEQ n, hEQ (n+1)] at hh
    have hf : (2:Int)^e*E n = (2:Int)^e*((2:Int)^(t n)*(2*E (n+1)-B)) := by
      calc
        _ = (2:Int)^(t n)*(2*((2:Int)^e*E (n+1))-(2:Int)^e*B) := hh
        _ = _ := by
          simp only [Int.mul_add, Int.mul_sub, Int.mul_assoc,
            Int.mul_left_comm, Int.mul_comm]
    have hcancel := Int.eq_of_mul_eq_mul_left
      (Int.pow_ne_zero (by decide : (2:Int)≠0)) hf
    exact hcancel
  let M : Nat := (E 0).natAbs + B.natAbs
  have hboundE0 : -(M:Int) ≤ E 0 ∧ E 0 ≤ (M:Int) := by
    have hu := Int.le_natAbs (a := E 0)
    have hl := Int.le_natAbs (a := -E 0)
    rw [Int.natAbs_neg] at hl
    dsimp [M]
    omega
  have hboundB : -(M:Int) ≤ B ∧ B ≤ (M:Int) := by
    have hu := Int.le_natAbs (a := B)
    have hl := Int.le_natAbs (a := -B)
    rw [Int.natAbs_neg] at hl
    dsimp [M]
    omega
  exact odd_difference_has_period M B E t hBodd hboundB hboundE0 hEnext

#print axioms difference_2adic_prefix
#print axioms difference_divisible_by_offset_power
#print axioms rescaled_odd_difference_has_period
end BB6.Agent9CrossFeeder
