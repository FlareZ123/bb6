import BB429Reset31
import BB429Even16
import Lean.Elab.Tactic.Omega

namespace BB429Branch7
open BB429Reset31
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000

/-- The branch-7 odd-reset family with first counter 7 modulo 32 has
no true blank-root ancestor once q is positive. The two forced inverse
steps end in the nonmodular (3 mod 4, 1 mod 4) obstruction. -/
theorem no_32q7 (q : Nat) (hq : 1 ≤ q) :
    ¬ Reach (32*q+7) (64*q+11) := by
  intro hr
  obtain ⟨x,y,hp,hs⟩ :=
    pred (32*q+7) (64*q+11) (by omega) hr
  obtain ⟨hfirst,hsecond⟩ :=
    BB429OddResetGate.incoming_odd_second x y (32*q+7) (64*q+11)
      hs (by omega)
  have hx : x=16*q+2 := by omega
  have hy : y=96*q+18 := by omega
  rw [hx,hy] at hp
  obtain ⟨x',y',hp',hs'⟩ :=
    pred (16*q+2) (96*q+18) (by omega) hp
  obtain ⟨hlin,hhalf,_⟩ :=
    BB429OddResetGate.incoming_even x' y' (16*q+2) (96*q+18)
      hs' (by omega) (by omega)
  have hx' : x'=40*q+3 := by omega
  have hy' : y'=48*q+9 := by omega
  rw [hx',hy'] at hp'
  obtain ⟨m,hm⟩ := hp'
  have hroot := BB429Even16.rooted_odd_three_one m
    (40*q+3) (48*q+9) hm (by omega) (by omega)
  omega

/-- The branch-7 odd-reset family with first counter 21 modulo 32
also has no true blank-root ancestor for q>=1. Its first inverse is
odd/even; the second inverse is forced to the F predecessor because
the second counter is 0 modulo 4. -/
theorem no_32q21 (q : Nat) (hq : 1 ≤ q) :
    ¬ Reach (32*q+21) (64*q+39) := by
  intro hr
  obtain ⟨x,y,hp,hs⟩ :=
    pred (32*q+21) (64*q+39) (by omega) hr
  obtain ⟨hfirst,hsecond⟩ :=
    BB429OddResetGate.incoming_odd_second x y (32*q+21) (64*q+39)
      hs (by omega)
  have hx : x=16*q+9 := by omega
  have hy : y=96*q+60 := by omega
  rw [hx,hy] at hp
  obtain ⟨x',y',hp',hs'⟩ :=
    pred (16*q+9) (96*q+60) (by omega) hp
  rcases odd_inverse x' y' (16*q+9) (96*q+60)
      (by omega) (by omega) hs' with hF | hS
  · obtain ⟨hfirst',hsecond'⟩ := hF
    have hx' : x'=8*q+3 := by omega
    have hy' : y'=112*q+69 := by omega
    rw [hx',hy'] at hp'
    obtain ⟨m,hm⟩ := hp'
    have hroot := BB429Even16.rooted_odd_three_one m
      (8*q+3) (112*q+69) hm (by omega) (by omega)
    omega
  · obtain ⟨_,_,hmod⟩ := hS
    omega

/-- Combined all-time exclusion of the two positive-parameter
branch-7 residue cylinders. -/
theorem no_32q7_or_21 (q : Nat) (hq : 1 ≤ q)
    (hr7 : Reach (32*q+7) (64*q+11) ∨
           Reach (32*q+21) (64*q+39)) : False := by
  rcases hr7 with h | h
  · exact no_32q7 q hq h
  · exact no_32q21 q hq h

#print axioms no_32q7
#print axioms no_32q21
#print axioms no_32q7_or_21
end BB429Branch7
