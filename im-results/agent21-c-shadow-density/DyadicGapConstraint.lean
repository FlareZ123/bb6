import DyadicReach

namespace BB6.Agent21Dyadic

/-- Every compatible nonempty inverse word starts with a gap whose parity
matches the exact source inverse branch, and that initial gap consumes a
power of two dividing the adjusted sum Q=x+y+(x+y)%2. This is the
mathematical interface between the dyadic word population and the
ModularCone recursive parent enumeration. -/
theorem first_gap_parity_and_divides
    (x y r b : Nat) (w : List Nat) (hr : 0<r) (hrb : r≤b)
    (hd : P b∣Z x y+acc (S x y) (r::w)) :
    r%2=(y+1)%2 ∧ P r∣-(((x+y+(x+y)%2:Nat):Int)) := by
  have hfirst : P r∣Z x y+offset (S x y) r := by
    have hbig : P r∣Z x y+acc (S x y) (r::w) :=
      Int.dvd_trans (P_dvd r b hrb) hd
    have hform : Z x y+acc (S x y) (r::w) =
        (Z x y+offset (S x y) r)+P r*acc (S x y+shift r) w := by
      simp only [acc]
      omega
    rw [hform] at hbig
    have hmul : P r∣P r*acc (S x y+shift r) w :=
      Int.dvd_mul_right _ _
    have hsub := Int.dvd_sub hbig hmul
    convert hsub using 1 <;> omega
  have htwo : (Z x y+offset (S x y) r)%2=0 := by
    have hh : P 1∣Z x y+offset (S x y) r :=
      Int.dvd_trans (P_dvd 1 r hr) hfirst
    simpa [P] using (Int.emod_eq_zero_of_dvd hh)
  have hpar : r%2=(y+1)%2 := by
    rw [one_numer] at htwo
    unfold parity S shift at htwo
    omega
  refine ⟨hpar,?_⟩
  have hq : Z x y+offset (S x y) r =
      -(((x+y+(x+y)%2:Nat):Int)) := by
    rw [one_numer,parity_cost x y r hpar]
    push_cast
    omega
  rw [←hq]
  exact hfirst

/-- If Q is not divisible by the entire available precision, a genuine
    leading inverse word gap cannot use up all those bits. -/
theorem first_gap_strict
    (x y r b : Nat) (w : List Nat) (hr : 0<r) (hrb : r≤b)
    (hd : P b∣Z x y+acc (S x y) (r::w))
    (hnot : ¬P b∣-(((x+y+(x+y)%2:Nat):Int))) : r<b := by
  have hq := (first_gap_parity_and_divides x y r b w hr hrb hd).2
  have he : r≠b := by
    intro h
    subst r
    exact hnot hq
  omega

#print axioms first_gap_parity_and_divides
#print axioms first_gap_strict
end BB6.Agent21Dyadic
