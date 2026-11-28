import SignedPairWordBridge
import FinitePrimitiveNoGo

namespace SignedPairMacroBridge
open FiniteCyclicValuation

private theorem pairRun_input_even_local {typ : Bool}
    {j u D v d' : Nat} (hp : PairRun typ j u D v d') : D%2=0 := by
  cases hp <;> omega

private theorem sourceWalk_input_even {x : PeriodicMacro.Letter}
    {xs : List PeriodicMacro.Letter} {u D U D' : Nat}
    (h : SourceWalk (x::xs) u D U D') : D%2=0 := by
  cases h with
  | @cons x xs u D v d' U D' hp rest =>
      exact pairRun_input_even_local hp

/-- Source-certified signed E/S+even-F primitive-power obstruction. The only
    hypotheses beyond literal SourceWalk repetitions are the exact quantitative
    threshold and finite cyclic primitivity of the positive exponent word. -/
theorem source_no_primitive_finite_power
    (x : PeriodicMacro.Letter) (xs : List PeriodicMacro.Letter)
    (u D : Nat → Nat) (n r0 : Nat)
    (hs : ∀ i : Nat, i≤n+1 →
      SourceWalk (x::xs) (u i) (D i) (u (i+1)) (D (i+1)))
    (hr0 : 6*u 0+D 0=2*r0)
    (hbig : 2*((r0+2*PeriodicMacro.T (x::xs))/3) <
      (PeriodicMacro.M (x::xs))^n)
    (hj : ∀ y : PeriodicMacro.Letter, y∈x::xs → 0<y.j)
    (hlarge : ∃ y : PeriodicMacro.Letter, y∈x::xs ∧ 1<y.j)
    (hprim : CyclicPrimitive (by simp : 0<(x::xs).length)
      (PeriodicMacro.slopeExponentFun (x::xs))) : False := by
  let r : Nat → Nat := fun i => (6*u i+D i)/2
  have hh (i : Nat) (hi : i≤n+1) :
      PeriodicMacro.Walk (x::xs) (u i) (r i)
        (u (i+1)) (r (i+1)) := by
    have hw := hs i hi
    have hpar := sourceWalk_input_even hw
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
  have hlargeBound : 2*((r 0+2*PeriodicMacro.T (x::xs))/3) <
      (PeriodicMacro.M (x::xs))^n := by
    rw [hr00]
    exact hbig
  exact PeriodicMacro.no_primitive_finite_power x xs u r n hh
    (hsafe 0) (hsafe 1) (hsafe 2) hlargeBound hj hlarge hprim

#print axioms source_no_primitive_finite_power

/-- Direct usable repetition bound: every literal signed-source repetition of a
    primitive positive-j word with a genuine F run stays below the exact
    finite-power rigidity threshold. -/
theorem source_primitive_power_bound
    (x : PeriodicMacro.Letter) (xs : List PeriodicMacro.Letter)
    (u D : Nat → Nat) (n r0 : Nat)
    (hs : ∀ i : Nat, i≤n+1 →
      SourceWalk (x::xs) (u i) (D i) (u (i+1)) (D (i+1)))
    (hr0 : 6*u 0+D 0=2*r0)
    (hj : ∀ y : PeriodicMacro.Letter, y∈x::xs → 0<y.j)
    (hlarge : ∃ y : PeriodicMacro.Letter, y∈x::xs ∧ 1<y.j)
    (hprim : CyclicPrimitive (by simp : 0<(x::xs).length)
      (PeriodicMacro.slopeExponentFun (x::xs))) :
    (PeriodicMacro.M (x::xs))^n ≤
      2*((r0+2*PeriodicMacro.T (x::xs))/3) := by
  by_cases hle : (PeriodicMacro.M (x::xs))^n ≤
      2*((r0+2*PeriodicMacro.T (x::xs))/3)
  · exact hle
  · have hbig : 2*((r0+2*PeriodicMacro.T (x::xs))/3) <
        (PeriodicMacro.M (x::xs))^n := by omega
    exact False.elim (source_no_primitive_finite_power x xs u D n r0 hs
      hr0 hbig hj hlarge hprim)

#print axioms source_primitive_power_bound
end SignedPairMacroBridge
