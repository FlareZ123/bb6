import SpaceNeedleClosed
import IndexPotential
import Lean.Elab.Tactic.Omega

namespace BB6.Agent20NeedlePotentialSource
open BB6.Agent48.SpaceNeedle
open BB6.Agent20IndexPotential
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

/-- A genuine high-level source chain in which every edge has the same dyadic
valuation w. The counter is the unshifted original d; the abstract affine
potential uses b=d+2. -/
inductive SourceChain (w : Nat) : Nat → Nat → Nat → Prop
  | zero (d : Nat) : SourceChain w 0 d d
  | step {k e f : Nat} (q : Nat)
      (he : highLevelNext (.N (oddTower q w)) = some (.N e))
      (tail : SourceChain w k (oddTower q w) f) :
      SourceChain w (k+1) e f

private theorem target_of_successor (w q e : Nat)
  (he : highLevelNext (.N (oddTower q w)) = some (.N e)) :
  e = oddTower q w + w + 3*(q+1) := by
  have hs : highLevelNext (.N (oddTower q w)) =
       some (.N (oddTower q w + w + 3*(q+1))) :=
    (highLevelNext_iff_oddTower _ _).mpr ⟨q,w,rfl,rfl⟩
  rw [hs] at he
  simp only [Option.some.injEq, HighLevelState.N.injEq] at he
  omega

private theorem edge3 (q e : Nat)
  (he : highLevelNext (.N (oddTower q 3)) = some (.N e)) :
  16*(e+2)=19*(oddTower q 3+2)+24 := by
  have hn := target_of_successor 3 q e he
  rw [hn]
  simp [oddTower]
  omega

private theorem edge4 (q e : Nat)
  (he : highLevelNext (.N (oddTower q 4)) = some (.N e)) :
  32*(e+2)=35*(oddTower q 4+2)+80 := by
  have hn := target_of_successor 4 q e he
  rw [hn]
  simp [oddTower]
  omega

private theorem edge5 (q e : Nat)
  (he : highLevelNext (.N (oddTower q 5)) = some (.N e)) :
  64*(e+2)=67*(oddTower q 5+2)+224 := by
  have hn := target_of_successor 5 q e he
  rw [hn]
  simp [oddTower]
  omega

private theorem source_to_affine {w L D d : Nat}
  (edge : ∀ q e, highLevelNext (.N (oddTower q w)) = some (.N e) →
    L*(e+2)=D*(oddTower q w+2)+d)
  {k e f : Nat} (hs : SourceChain w k e f) :
  Chain L D d k (e+2) (f+2) := by
  induction hs with
  | zero x => exact .zero (x+2)
  | @step j e f q he ht ih =>
    exact .step (edge q e he) ih

/-- An all-depth fixed-valuation-three original-source reverse chain
can only start at shifted counter satisfying 19^k ∣ 3*(e+2)+24. -/
theorem valuationThreeSource {k e f : Nat} (h : SourceChain 3 k e f) :
  19^k ∣ 3*(e+2)+24 :=
  valuationThree (source_to_affine edge3 h)

/-- Original-source fixed-valuation-four necessary congruence. -/
theorem valuationFourSource {k e f : Nat} (h : SourceChain 4 k e f) :
  35^k ∣ 3*(e+2)+80 :=
  valuationFour (source_to_affine edge4 h)

/-- Original-source fixed-valuation-five necessary congruence. -/
theorem valuationFiveSource {k e f : Nat} (h : SourceChain 5 k e f) :
  67^k ∣ 3*(e+2)+224 :=
  valuationFive (source_to_affine edge5 h)

#print axioms valuationThreeSource
#print axioms valuationFourSource
#print axioms valuationFiveSource
end BB6.Agent20NeedlePotentialSource
