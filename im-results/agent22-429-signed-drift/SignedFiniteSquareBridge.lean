import SignedFinitePowerBridge
import FiniteSquareRigidity

/-! The two-copy and three-copy modular gap obstruction for actual guarded signed
E/S+even-F SourceWalk words. Original BB429 TM lift is separate. -/
namespace SignedPairMacroBridge

/-- Two actual guarded signed typed-word copies force a bounded signed
    lattice offset modulo the word's exact transfer scale. -/
theorem source_two_copy_gap (x : PeriodicMacro.Letter)
    (xs : List PeriodicMacro.Letter)
    (u0 D0 u1 D1 u2 D2 r0 : Nat)
    (h0 : SourceWalk (x::xs) u0 D0 u1 D1)
    (h1 : SourceWalk (x::xs) u1 D1 u2 D2)
    (hr0 : 6*u0+D0=2*r0) :
    ∃ k : Int,
      -(((r0+PeriodicMacro.T (x::xs))/3):Int) ≤
        ((PeriodicMacro.A (x::xs)*PeriodicMacro.T (x::xs)):Int)-
          (PeriodicMacro.M (x::xs):Int)*k ∧
      ((PeriodicMacro.A (x::xs)*PeriodicMacro.T (x::xs)):Int)-
          (PeriodicMacro.M (x::xs):Int)*k ≤ ((r0/3):Int) := by
  obtain ⟨r1,hr1,w0⟩ := sourceWalk_model h0 r0 hr0
  obtain ⟨r2,hr2,w1⟩ := sourceWalk_model h1 r1 hr1
  obtain ⟨hm0,ht0⟩ := PeriodicMacro.transfer w0
  obtain ⟨hm1,ht1⟩ := PeriodicMacro.transfer w1
  have hm1' : PeriodicMacro.M (x::xs)*u2 =
      u1 + PeriodicMacro.A (x::xs)*(r0+PeriodicMacro.T (x::xs))+
        PeriodicMacro.B (x::xs) := by
    rw [ht0] at hm1
    exact hm1
  have hsafe0 : 3*u0≤r0 := by omega
  have hsafe1 : 3*u1≤r0+PeriodicMacro.T (x::xs) := by
    rw [← ht0]
    omega
  exact PeriodicSquare.two_transfers_gap
    (PeriodicMacro.M (x::xs))
    (PeriodicMacro.A (x::xs))
    (PeriodicMacro.B (x::xs))
    (PeriodicMacro.T (x::xs))
    u0 u1 u2 r0 hm0 hm1' hsafe0 hsafe1

/-- The source guard at the start of a genuine third copy forces
    u2-u1 to be even. It upgrades the two-copy modulus M to 2M. -/
theorem source_three_copy_even_gap (x : PeriodicMacro.Letter)
    (xs : List PeriodicMacro.Letter)
    (u0 D0 u1 D1 u2 D2 u3 D3 r0 : Nat)
    (h0 : SourceWalk (x::xs) u0 D0 u1 D1)
    (h1 : SourceWalk (x::xs) u1 D1 u2 D2)
    (h2 : SourceWalk (x::xs) u2 D2 u3 D3)
    (hr0 : 6*u0+D0=2*r0) :
    ∃ k : Int,
      -(((r0+PeriodicMacro.T (x::xs))/3):Int) ≤
        ((PeriodicMacro.A (x::xs)*PeriodicMacro.T (x::xs)):Int)-
          (2*(PeriodicMacro.M (x::xs):Int))*k ∧
      ((PeriodicMacro.A (x::xs)*PeriodicMacro.T (x::xs)):Int)-
          (2*(PeriodicMacro.M (x::xs):Int))*k ≤ ((r0/3):Int) := by
  obtain ⟨r1,hr1,w0⟩ := sourceWalk_model h0 r0 hr0
  obtain ⟨r2,hr2,w1⟩ := sourceWalk_model h1 r1 hr1
  obtain ⟨hm0,ht0⟩ := PeriodicMacro.transfer w0
  obtain ⟨hm1,ht1⟩ := PeriodicMacro.transfer w1
  have hm1' : PeriodicMacro.M (x::xs)*u2 =
      u1 + PeriodicMacro.A (x::xs)*(r0+PeriodicMacro.T (x::xs))+
        PeriodicMacro.B (x::xs) := by
    rw [ht0] at hm1
    exact hm1
  have hsafe0 : 3*u0≤r0 := by omega
  have hsafe1 : 3*u1≤r0+PeriodicMacro.T (x::xs) := by
    rw [← ht0]
    omega
  have hp1 := sourceWalk_head_parity h1
  have hp2 := sourceWalk_head_parity h2
  have hpar : u1%2=u2%2 := by omega
  exact PeriodicSquare.triple_entry_even_gap
    (PeriodicMacro.M (x::xs))
    (PeriodicMacro.A (x::xs))
    (PeriodicMacro.B (x::xs))
    (PeriodicMacro.T (x::xs))
    u0 u1 u2 r0 hm0 hm1' hsafe0 hsafe1 hpar

#print axioms source_two_copy_gap
#print axioms source_three_copy_even_gap
end SignedPairMacroBridge
