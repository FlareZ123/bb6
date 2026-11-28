import Q0151FiniteModel

set_option maxHeartbeats 0
namespace BB6.Agent5Q0151Preimage
open BB6.Agent5Q0151FiniteModel

/-!
The q0-151 automaton has two live modes N/P and one reject value -1.
A suffix mask is a bitset representing exactly which live modes accept.
The backward preimage step commutes with the forward mode map. This is
the key algebraic lemma for proving segConcat represents concrete bit
concatenation rather than merely checking the abstract fixed point.
-/

theorem mask_pre_zero (c t : Nat) :
    maskAccept (pre c t) 0 = maskAccept t (dnext 0 c) := by
  cases h0 : maskAccept t (dnext 0 c) <;>
    cases h1 : maskAccept t (dnext 1 c) <;>
    simp only [pre,h0,h1,ite_true,ite_false] <;> decide

theorem mask_pre_one (c t : Nat) :
    maskAccept (pre c t) 1 = maskAccept t (dnext 1 c) := by
  cases h0 : maskAccept t (dnext 0 c) <;>
    cases h1 : maskAccept t (dnext 1 c) <;>
    simp only [pre,h0,h1,ite_true,ite_false] <;> decide

def LiveMode (g : Int) : Prop :=
  g = -1 ∨ g = 0 ∨ g = 1

theorem mask_pre_mode (g : Int) (c t : Nat) (hg : LiveMode g) :
    maskAccept (pre c t) g = maskAccept t (dnext g c) := by
  rcases hg with h | h | h
  · subst g
    simp [maskAccept,dnext]
  · subst g
    exact mask_pre_zero c t
  · subst g
    exact mask_pre_one c t

def pairPre (fN fP : Int) (t : Nat) : Nat :=
  (if maskAccept t fN then 1 else 0) +
  (if maskAccept t fP then 2 else 0)

theorem pair_pre_step (fN fP : Int) (c t : Nat)
    (hN : LiveMode fN) (hP : LiveMode fP) :
    pairPre fN fP (pre c t) =
      pairPre (dnext fN c) (dnext fP c) t := by
  simp only [pairPre,mask_pre_mode fN c t hN,mask_pre_mode fP c t hP]

#print axioms mask_pre_zero
#print axioms mask_pre_one
#print axioms pair_pre_step
end BB6.Agent5Q0151Preimage
