import FinitePowerMacro
import FiniteSlopeCycle
import FiniteSlopeCone

namespace PeriodicMacro

/-- A sufficiently long exact finite power of a positive-j word containing a
    genuine F run produces a closed positive slope cycle in the strict cone. -/
theorem finite_power_gives_strict_slope_cycle
    (x : Letter) (xs : List Letter) (u r : Nat → Nat) (n : Nat)
    (hw : ∀ i : Nat, i≤n+1 →
      Walk (x::xs) (u i) (r i) (u (i+1)) (r (i+1)))
    (hsafe0 : 3*u 0≤r 0)
    (hsafe1 : 3*u 1≤r 1)
    (hsafe2 : 3*u 2≤r 2)
    (hbig : 2*((r 0+2*T (x::xs))/3)<(M (x::xs))^n)
    (hj : ∀ y : Letter, y∈x::xs → 0<y.j)
    (hlarge : ∃ y : Letter, y∈x::xs ∧ 1<y.j) :
    ∃ d : Nat, 0<d ∧ 3*d<T (x::xs) ∧
      SlopeWalk (T (x::xs)) (x::xs) d d := by
  have hrigid := finite_power_word_slope (x::xs) u r n hw
    hsafe0 hsafe1 hsafe2 hbig
  have hcone := affine_equation_strict_slope x xs (u 0) (u 1)
    hj hlarge hrigid.2
  have h0 := hw 0 (by omega)
  have h1 := hw 1 (by omega)
  have hcycle := affine_two_walks_give_slope_cycle h0 h1
    (Nat.le_of_lt hcone.1) (by exact_mod_cast hrigid.1)
  obtain ⟨d,hd0,hd1,hslope⟩ := hcycle
  have hd : u 1-u 0=d :=
    (Nat.sub_eq_iff_eq_add' (Nat.le_of_lt hcone.1)).2 hd0
  subst d
  exact ⟨u 1-u 0, by omega, hcone.2, hslope⟩

#print axioms finite_power_gives_strict_slope_cycle
end PeriodicMacro
