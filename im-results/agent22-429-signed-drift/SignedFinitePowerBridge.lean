import SignedPairWordBridge
import FinitePowerMacro

/-!
Exact source-typed signed E/S-plus-even-F finite power bridge.
This is the original signed macro system, not yet the original #429 TM.
Lean kernel acceptance is pending CI compilation and axiom inspection.
-/
namespace SignedPairMacroBridge

theorem sourceWalk_head_even {x : PeriodicMacro.Letter}
    {xs : List PeriodicMacro.Letter} {u D U D' : Nat}
    (h : SourceWalk (x::xs) u D U D') : D%2=0 := by
  cases h with
  | cons hp rest =>
    cases hp <;> omega

theorem sourceWalk_head_parity {x : PeriodicMacro.Letter}
    {xs : List PeriodicMacro.Letter} {u D U D' : Nat}
    (h : SourceWalk (x::xs) u D U D') :
    u%2 = (if x.isE then 1 else 0) := by
  cases h with
  | cons hp rest =>
    cases hp <;> simp_all

/-- n+2 consecutive repetitions of a nonempty source-exact typed
    pair/F word have a rigid affine slope whenever M^n beats the first
    three source half-rank heights. -/
theorem source_finite_power_slope (x : PeriodicMacro.Letter)
    (xs : List PeriodicMacro.Letter) (u D : Nat → Nat)
    (n r0 : Nat)
    (hs : ∀ i : Nat, i ≤ n+1 →
      SourceWalk (x::xs) (u i) (D i) (u (i+1)) (D (i+1)))
    (hr0 : 6*u 0+D 0=2*r0)
    (hbig : 2*((r0+2*PeriodicMacro.T (x::xs))/3) <
      (PeriodicMacro.M (x::xs))^n) :
    (u 0:Int)+(u 2:Int)=2*(u 1:Int) ∧
    ((PeriodicMacro.M (x::xs):Int)-1)*
      ((u 1:Int)-(u 0:Int)) =
      ((PeriodicMacro.A (x::xs)*PeriodicMacro.T (x::xs)):Int) := by
  let r : Nat → Nat := fun i => (6*u i+D i)/2
  have hh (i : Nat) (hi : i≤n+1) :
      PeriodicMacro.Walk (x::xs) (u i) (r i)
        (u (i+1)) (r (i+1)) := by
    have hw := hs i hi
    have hpar := sourceWalk_head_even hw
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
  have hlarge : 2*((r 0+2*PeriodicMacro.T (x::xs))/3) <
      (PeriodicMacro.M (x::xs))^n := by
    rw [hr00]
    exact hbig
  exact PeriodicMacro.finite_power_word_slope
    (x::xs) u r n hh (hsafe 0) (hsafe 1) (hsafe 2) hlarge

/-- An exact signed-word power above the quantitative threshold requires
    2*(M-1) to divide A*T. The parity input is not assumed: it is
    supplied by the actual E/S branch guards in SourceWalk. -/
theorem source_finite_power_even_divisibility
    (x : PeriodicMacro.Letter) (xs : List PeriodicMacro.Letter)
    (u D : Nat → Nat) (n r0 : Nat)
    (hs : ∀ i : Nat, i≤n+1 →
      SourceWalk (x::xs) (u i) (D i) (u (i+1)) (D (i+1)))
    (hr0 : 6*u 0+D 0=2*r0)
    (hbig : 2*((r0+2*PeriodicMacro.T (x::xs))/3) <
      (PeriodicMacro.M (x::xs))^n) :
    (2*((PeriodicMacro.M (x::xs):Int)-1)) ∣
      ((PeriodicMacro.A (x::xs)*PeriodicMacro.T (x::xs)):Int) := by
  have hp0 := sourceWalk_head_parity (hs 0 (by omega))
  have hp1 := sourceWalk_head_parity (hs 1 (by omega))
  have hpar : u 0%2=u 1%2 := by omega
  have hrigid := (source_finite_power_slope x xs u D n r0 hs hr0 hbig).2
  obtain ⟨k,hk⟩ : ∃ k : Int,
      (u 1:Int)-(u 0:Int)=2*k := by
    refine ⟨((u 1:Int)-(u 0:Int))/2,?_⟩
    omega
  refine ⟨k,?_⟩
  calc
    ((PeriodicMacro.A (x::xs)*PeriodicMacro.T (x::xs)):Int) =
      ((PeriodicMacro.M (x::xs):Int)-1)*
        ((u 1:Int)-(u 0:Int)) := hrigid.symm
    _ = (2*((PeriodicMacro.M (x::xs):Int)-1))*k := by
      rw [hk]
      ac_rfl

#print axioms sourceWalk_head_even
#print axioms sourceWalk_head_parity
#print axioms source_finite_power_slope
#print axioms source_finite_power_even_divisibility
end SignedPairMacroBridge
