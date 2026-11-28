import DoubledGapCycle

namespace PeriodicMacro
open FiniteCyclicValuation

/-- Finite-power closure of the doubled typed-period case. -/
theorem no_doubled_gap_finite_power
    (x : Letter) (xs : List Letter) (u r : Nat → Nat) (n : Nat)
    (hw : ∀ i : Nat, i≤n+1 →
      Walk ((x::xs)++flipWord (x::xs)) (u i) (r i)
        (u (i+1)) (r (i+1)))
    (hsafe0 : 3*u 0≤r 0)
    (hsafe1 : 3*u 1≤r 1)
    (hsafe2 : 3*u 2≤r 2)
    (hbig : 2*((r 0+2*T ((x::xs)++flipWord (x::xs)))/3) <
      M ((x::xs)++flipWord (x::xs))^n)
    (hj : ∀ y : Letter, y∈x::xs → 0<y.j)
    (hlarge : ∃ y : Letter, y∈x::xs ∧ 1<y.j)
    (hprim : CyclicPrimitive (by simp : 0<(x::xs).length)
      (slopeExponentFun (x::xs))) : False := by
  let core := x::xs
  let tail := xs++flipWord core
  have hjflip : ∀ y : Letter, y∈flipWord core → 0<y.j := by
    intro y hy
    unfold flipWord at hy
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hy
    simpa using hj z (by simpa [core] using hz)
  have hjfull : ∀ y : Letter, y∈x::tail → 0<y.j := by
    intro y hy
    rcases List.mem_cons.mp hy with hxy | htail
    · subst y
      exact hj x (by simp)
    · unfold tail at htail
      rcases List.mem_append.mp htail with hxs | hflip
      · exact hj y (by simp [hxs])
      · exact hjflip y hflip
  have hlargefull : ∃ y : Letter, y∈x::tail ∧ 1<y.j := by
    obtain ⟨y,hy,hyj⟩ := hlarge
    refine ⟨y,?_,hyj⟩
    rcases List.mem_cons.mp hy with hxy | hxs
    · exact List.mem_cons.mpr (Or.inl hxy)
    · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl hxs)))
  have hw' : ∀ i : Nat, i≤n+1 →
      Walk (x::tail) (u i) (r i) (u (i+1)) (r (i+1)) := by
    intro i hi
    simpa [tail,core] using hw i hi
  have hbig' : 2*((r 0+2*T (x::tail))/3)<M (x::tail)^n := by
    simpa [tail,core] using hbig
  obtain ⟨d,hd,hcone,hcycle⟩ :=
    finite_power_gives_strict_slope_cycle x tail u r n hw'
      hsafe0 hsafe1 hsafe2 hbig' hjfull hlargefull
  exact no_doubled_gap_slope_cycle x xs
    (by simpa [tail,core] using hcycle) hj hlarge hd
    (by simpa [tail,core] using hcone) hprim

#print axioms no_doubled_gap_finite_power
end PeriodicMacro
