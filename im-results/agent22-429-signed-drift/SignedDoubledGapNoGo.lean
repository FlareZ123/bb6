import SignedFinitePowerBridge
import DoubledGapFinitePower

namespace SignedPairMacroBridge
open FiniteCyclicValuation

/-- Signed-source closure of the doubled typed-period case. -/
theorem source_no_doubled_gap_finite_power
    (x : PeriodicMacro.Letter) (xs : List PeriodicMacro.Letter)
    (u D : Nat → Nat) (n r0 : Nat)
    (hs : ∀ i : Nat, i≤n+1 →
      SourceWalk ((x::xs)++PeriodicMacro.flipWord (x::xs))
        (u i) (D i) (u (i+1)) (D (i+1)))
    (hr0 : 6*u 0+D 0=2*r0)
    (hbig : 2*((r0+2*PeriodicMacro.T
      ((x::xs)++PeriodicMacro.flipWord (x::xs)))/3) <
      PeriodicMacro.M ((x::xs)++PeriodicMacro.flipWord (x::xs))^n)
    (hj : ∀ y : PeriodicMacro.Letter, y∈x::xs → 0<y.j)
    (hlarge : ∃ y : PeriodicMacro.Letter, y∈x::xs ∧ 1<y.j)
    (hprim : CyclicPrimitive (by simp : 0<(x::xs).length)
      (PeriodicMacro.slopeExponentFun (x::xs))) : False := by
  let full := (x::xs)++PeriodicMacro.flipWord (x::xs)
  let r : Nat → Nat := fun i => (6*u i+D i)/2
  have hh (i : Nat) (hi : i≤n+1) :
      PeriodicMacro.Walk full (u i) (r i)
        (u (i+1)) (r (i+1)) := by
    have hw := hs i hi
    have hpar : D i%2=0 := by
      have hp := sourceWalk_head_even (by simpa [full] using hw)
      exact hp
    have hin : 6*u i+D i=2*r i := by
      dsimp [r]
      omega
    obtain ⟨s,hout,walk⟩ := sourceWalk_model hw (r i) hin
    have heq : s=r (i+1) := by
      dsimp [r]
      omega
    simpa only [heq] using walk
  have hsafe (i : Nat) : 3*u i≤r i := by
    dsimp [r]
    omega
  have hr00 : r 0=r0 := by
    dsimp [r]
    omega
  have hlargeBound : 2*((r 0+2*PeriodicMacro.T full)/3) <
      PeriodicMacro.M full^n := by
    rw [hr00]
    simpa [full] using hbig
  apply PeriodicMacro.no_doubled_gap_finite_power x xs u r n
  · intro i hi
    simpa [full] using hh i hi
  · exact hsafe 0
  · exact hsafe 1
  · exact hsafe 2
  · simpa [full] using hlargeBound
  · exact hj
  · exact hlarge
  · exact hprim

/-- Direct usable bound for a signed doubled typed period. -/
theorem source_doubled_gap_power_bound
    (x : PeriodicMacro.Letter) (xs : List PeriodicMacro.Letter)
    (u D : Nat → Nat) (n r0 : Nat)
    (hs : ∀ i : Nat, i≤n+1 →
      SourceWalk ((x::xs)++PeriodicMacro.flipWord (x::xs))
        (u i) (D i) (u (i+1)) (D (i+1)))
    (hr0 : 6*u 0+D 0=2*r0)
    (hj : ∀ y : PeriodicMacro.Letter, y∈x::xs → 0<y.j)
    (hlarge : ∃ y : PeriodicMacro.Letter, y∈x::xs ∧ 1<y.j)
    (hprim : CyclicPrimitive (by simp : 0<(x::xs).length)
      (PeriodicMacro.slopeExponentFun (x::xs))) :
    PeriodicMacro.M ((x::xs)++PeriodicMacro.flipWord (x::xs))^n ≤
      2*((r0+2*PeriodicMacro.T
        ((x::xs)++PeriodicMacro.flipWord (x::xs)))/3) := by
  by_cases hle : PeriodicMacro.M
      ((x::xs)++PeriodicMacro.flipWord (x::xs))^n ≤
      2*((r0+2*PeriodicMacro.T
        ((x::xs)++PeriodicMacro.flipWord (x::xs)))/3)
  · exact hle
  · have hbig : 2*((r0+2*PeriodicMacro.T
        ((x::xs)++PeriodicMacro.flipWord (x::xs)))/3) <
        PeriodicMacro.M ((x::xs)++PeriodicMacro.flipWord (x::xs))^n := by omega
    exact False.elim (source_no_doubled_gap_finite_power x xs u D n r0
      hs hr0 hbig hj hlarge hprim)

#print axioms source_no_doubled_gap_finite_power
#print axioms source_doubled_gap_power_bound
end SignedPairMacroBridge
