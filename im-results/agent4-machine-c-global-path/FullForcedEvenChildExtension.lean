import FullForcedFilter
import EvenChild
import HighEvenRightC23FullForcedResidual
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent4EvenChildExtension

open BB6.Agent3
open BB6.Agent3FullForcedResidual
open BB6.Agent46

/-- Fifth exact forced-parent sector omitted by the four-gate normalizer:
    odd x, even y>=4, and x+y=3 mod 8 have exactly one source parent. -/
def evenChildGate (x y : Nat) : Bool :=
  decide (x%2=1 ∧ y%2=0 ∧ 4≤y ∧ (x+y)%8=3)

def evenChildParent (x y : Nat) : Nat × Nat :=
  (x+y-2,y/2-1)

/-- A genuine blank-reached point in the even-child sector forces its
    unique exact predecessor to be genuinely blank-reached. -/
theorem evenChild_parent_reach_of_reach (x y : Nat)
    (hgate : evenChildGate x y = true) :
    CReach x y → CReach (evenChildParent x y).1 (evenChildParent x y).2 := by
  intro hreach
  have hcond : x%2=1 ∧ y%2=0 ∧ 4≤y ∧ (x+y)%8=3 := by
    simpa [evenChildGate] using hgate
  rcases hcond with ⟨hx,hy,hy4,hs⟩
  rcases hreach with ⟨time,ht⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at ht
      omega
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none =>
          simp [BB6.Agent8Section.run,hp] at ht
      | some s =>
          rcases s with ⟨a,k⟩
          have hsEdge : secNext (a,k)=some (x,y) := by
            simpa [BB6.Agent8Section.run,hp] using ht
          obtain ⟨ha,hk⟩ :=
            (even_child_parent_iff a k x y hx hy hy4 hs).mp hsEdge
          have hparent :
              BB6.Agent8Section.run secNext n (some (5,1)) =
                some ((evenChildParent x y).1,(evenChildParent x y).2) := by
            rw [ha,hk] at hp
            simpa [evenChildParent] using hp
          exact ⟨n,hparent⟩

/-- Add the even-child forced-parent sector to the four-gate exact
    exclusion filter, provided its unique parent is already excluded. -/
def fullForcedExcludedPlus (x y : Nat) : Bool :=
  fullForcedExcluded x y ||
    (evenChildGate x y &&
      fullForcedExcluded (evenChildParent x y).1 (evenChildParent x y).2)

theorem fullForcedExcludedPlus_sound (x y : Nat)
    (hex : fullForcedExcludedPlus x y = true) :
    ∀ time, BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (x,y) := by
  intro time ht
  by_cases hbase : fullForcedExcluded x y = true
  · exact (fullForcedExcluded_sound x y hbase time) ht
  · have hparts :
        evenChildGate x y = true ∧
          fullForcedExcluded (evenChildParent x y).1
            (evenChildParent x y).2 = true := by
      simpa [fullForcedExcludedPlus,hbase] using hex
    have hpReach :
        CReach (evenChildParent x y).1 (evenChildParent x y).2 :=
      evenChild_parent_reach_of_reach x y hparts.1 ⟨time,ht⟩
    rcases hpReach with ⟨n,hn⟩
    exact fullForcedExcluded_sound (evenChildParent x y).1
      (evenChildParent x y).2 hparts.2 n hn

/-- The stronger high-parameter Boolean criterion. It retains the old
    C70+C23+all-phase+even-right sieve and adds the exact fifth sector. -/
def highAllowedC23WithEvenRightPlusBool (j m : Nat) : Bool :=
  highAllowedC23WithEvenRightBool j m &&
    fullForcedExcludedPlus (highTargetX j) (highTargetY j m)

theorem highAllowedC23WithEvenRightPlusBool_sound (j m : Nat)
    (h : highAllowedC23WithEvenRightPlusBool j m = true) :
    ∀ time, BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (highTargetX j,highTargetY j m) := by
  have hp : highAllowedC23WithEvenRightBool j m = true ∧
      fullForcedExcludedPlus (highTargetX j) (highTargetY j m) = true := by
    simpa [highAllowedC23WithEvenRightPlusBool] using h
  exact fullForcedExcludedPlus_sound (highTargetX j) (highTargetY j m) hp.2

#print axioms evenChild_parent_reach_of_reach
#print axioms fullForcedExcludedPlus_sound
#print axioms highAllowedC23WithEvenRightPlusBool_sound

end BB6.Agent4EvenChildExtension
