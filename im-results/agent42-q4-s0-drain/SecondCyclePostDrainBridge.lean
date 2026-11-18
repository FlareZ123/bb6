import Q4Suffix
import CountedSweep
import Lean.Elab.Tactic.Omega

/-!
# Finite bridges for the second positive-z S0 post-drain continuation

After the P2 endpoint and the full S0 drain, the natural left sweep can
reach head -3 with four zeros immediately behind it.  The machine then
uses the four-step 0000 bridge below, scans a contiguous rightward
one-run in state 1, and uses the eight-step 001001 bridge below to enter
state 4 at the start of the very large right unary counter.

The bridges are exact arbitrary-exterior-tape statements.  The source
draft does not claim the P2 endpoint hypotheses have yet been composed
with them.
-/

namespace BB6Coverage.Agent42SecondCyclePostDrain

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8CountedReset
open BB6Coverage.Agent24ChampionTime

/-- The four-step bridge from state 3 on four zeros to state 1. -/
def afterSecondCycleZero4 (T : Int → Bool) : Int → Bool :=
  fun x => if x = -4 ∨ x = -3 ∨ x = -2 then true else T x

theorem secondCycle_zero4_bridge (T : Int → Bool)
    (h3 : T (-3) = false)
    (h4 : T (-4) = false)
    (h2 : T (-2) = false) :
    run tm2 4 ⟨3,-3,T⟩ =
      some ⟨1,-1,afterSecondCycleZero4 T⟩ := by
  have t30 : tm2 ((3:Fin 6),false) = some ⟨false,false,2⟩ := rfl
  have t20 : tm2 ((2:Fin 6),false) = some ⟨true,true,4⟩ := rfl
  have t40 : tm2 ((4:Fin 6),false) = some ⟨true,true,0⟩ := rfl
  have t00 : tm2 ((0:Fin 6),false) = some ⟨true,true,1⟩ := rfl
  have e1 : -4 ≠ -3 := by omega
  have e2 : -3 ≠ -2 := by omega
  have e3 : -4 ≠ -2 := by omega
  simp [run,rawStep,readSlot,applyMove,h3,h4,h2,t30,t20,t40,t00,
    afterSecondCycleZero4,e1,e2,e3]
  funext x
  by_cases hx4 : x = -4 <;> by_cases hx3 : x = -3 <;>
    by_cases hx2 : x = -2 <;>
    simp [afterSecondCycleZero4,hx4,hx3,hx2]

/-- Local window for the eight-step state-1 to state-4 bridge. -/
def secondCycleEightInside (x : Int) : Bool :=
  decide (-3 ≤ x ∧ x ≤ 2)

def secondCycleEightStart : FConfig :=
  ⟨1,0,[-1,2]⟩

def secondCycleEightEnd : FConfig :=
  ⟨4,2,[-5,-4,-3,-1,0]⟩

theorem secondCycleEight_exact :
    fRun tm2 8 secondCycleEightStart = some secondCycleEightEnd := by
  decide

theorem secondCycleEight_heads :
    (List.range 8).all (fun k =>
      match fRun tm2 k secondCycleEightStart with
      | none => true
      | some f => secondCycleEightInside f.head) = true := by
  decide

/-- Exact eight-step bridge over an arbitrary exterior tape:
state 1 at g sees 001001 and becomes state 4 at g+2. -/
theorem secondCycle_eight_bridge (T : Int → Bool) (g : Int)
    (h0 : T (g-3) = false)
    (h1 : T (g-2) = false)
    (h2 : T (g-1) = true)
    (h3 : T g = false)
    (h4 : T (g+1) = false)
    (h5 : T (g+2) = true) :
    run tm2 8 ⟨1,g,T⟩ =
      some (frameAt T g secondCycleEightInside secondCycleEightEnd) := by
  apply bridgeAt T g secondCycleEightInside
    secondCycleEightStart secondCycleEightEnd 8 rfl
    secondCycleEight_exact secondCycleEight_heads
  intro x hx
  have hrange : -3 ≤ x ∧ x ≤ 2 := by
    simpa [secondCycleEightInside] using hx
  have hcases :
      x=(-3) ∨ x=(-2) ∨ x=(-1) ∨ x=0 ∨ x=1 ∨ x=2 := by omega
  rcases hcases with hx0|hx1|hx2|hx3|hx4|hx5
  · subst x
    simpa using h0
  · subst x
    simpa using h1
  · subst x
    simpa using h2
  · subst x
    simpa using h3
  · subst x
    simpa using h4
  · subst x
    simpa using h5

#print axioms secondCycle_zero4_bridge
#print axioms secondCycleEight_exact
#print axioms secondCycle_eight_bridge

end BB6Coverage.Agent42SecondCyclePostDrain
