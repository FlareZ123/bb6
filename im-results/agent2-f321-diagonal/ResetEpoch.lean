import DiagonalCoordinates
import Lean.Elab.Tactic.Omega

/-!
Reset-to-reset epoch skeleton for the exact F321 counter map.

Between consecutive Middle resets, only High/Far outer moves occur.  The
diagonal coordinate X=a+d+5 strictly increases on every such outer move, and
the next Middle reset's first counter 4a+6 lies strictly above the pre-reset X.
Consequently the first counter of every reset-to-reset epoch is strictly
increasing.  This supplies a well-founded global coordinate for future maximal
epoch decompositions.
-/

namespace BB6.Agent2F321ResetEpoch
open BB6.Agent31F321Density
open BB6.Agent2F321Diagonal

/-- Exactly one High or Far source move, written without branch ambiguity. -/
def OuterMove (a d A D : Nat) : Prop :=
  (d+2 ≤ a ∧ A=a-d-2 ∧ D=2*d+3) ∨
  (a<d ∧ 3*a+1≤d ∧ A=4*a+6 ∧ D=d-3*a)

/-- Arbitrary finite High/Far interleaving. -/
inductive OuterRun : Nat → Nat → Nat → Nat → Nat → Prop
  | nil (a d) : OuterRun 0 a d a d
  | step {n a d A D B C} :
      OuterRun n a d A D → OuterMove A D B C →
      OuterRun (n+1) a d B C

/-- Exactly one Middle reset, including its parity-selected output counter. -/
def ResetMove (a d R c : Nat) : Prop :=
  (a<d ∧ d<3*a+1 ∧ (d-a)%2=0 ∧ R=4*a+6 ∧ c=2) ∨
  (a<d ∧ d<3*a+1 ∧ (d-a)%2=1 ∧ R=4*a+6 ∧ c=1)

/-- A reset epoch: a High/Far segment followed by the next Middle reset. -/
def ResetEpoch (R c R' c' : Nat) : Prop :=
  ∃ n a d, OuterRun n R c a d ∧ ResetMove a d R' c'

theorem outerMove_source {a d A D : Nat}
    (h : OuterMove a d A D) : CounterMove a d A D := by
  unfold OuterMove at h
  rcases h with h | h
  · rcases h with ⟨hg,rfl,rfl⟩
    exact CounterMove.high d hg
  · rcases h with ⟨h1,h2,rfl,rfl⟩
    exact CounterMove.far d h1 h2

theorem resetMove_source {a d R c : Nat}
    (h : ResetMove a d R c) : CounterMove a d R c := by
  unfold ResetMove at h
  rcases h with h | h
  · rcases h with ⟨h1,h2,hp,rfl,rfl⟩
    exact CounterMove.middleEven d h1 h2 hp
  · rcases h with ⟨h1,h2,hp,rfl,rfl⟩
    exact CounterMove.middleOdd d h1 h2 hp

/-- X strictly increases on every outer move: +1 for High, +6 for Far. -/
theorem outerMove_X_strict {a d A D : Nat}
    (h : OuterMove a d A D) : X a d < X A D := by
  unfold OuterMove at h
  rcases h with h | h
  · rcases h with ⟨hg,rfl,rfl⟩
    have hx := (high_coordinates a d hg).1
    omega
  · rcases h with ⟨h1,h2,rfl,rfl⟩
    have hx := (far_coordinates a d h1 h2).1
    omega

theorem outerRun_X_monotone {n a d A D : Nat}
    (h : OuterRun n a d A D) : X a d ≤ X A D := by
  induction h with
  | nil => exact Nat.le_refl _
  | step h hm ih =>
      have hs := outerMove_X_strict hm
      omega

/-- The next reset first counter lies strictly above the coordinate immediately
    before the reset. -/
theorem resetMove_output_above_X {a d R c : Nat}
    (h : ResetMove a d R c) : X a d < R := by
  unfold ResetMove at h
  rcases h with h | h
  · rcases h with ⟨h1,h2,hp,rfl,rfl⟩
    unfold X
    omega
  · rcases h with ⟨h1,h2,hp,rfl,rfl⟩
    unfold X
    omega

/-- Reset first counters are strictly increasing from one reset epoch to the
    next, independent of the High/Far interleaving length and branch pattern. -/
theorem resetEpoch_strict {R c R' c' : Nat}
    (h : ResetEpoch R c R' c') : R < R' := by
  rcases h with ⟨n,a,d,ho,hr⟩
  have h0 : R < X R c := by
    unfold X
    omega
  have h1 := outerRun_X_monotone ho
  have h2 := resetMove_output_above_X hr
  omega

#print axioms outerMove_source
#print axioms resetMove_source
#print axioms resetEpoch_strict
end BB6.Agent2F321ResetEpoch
