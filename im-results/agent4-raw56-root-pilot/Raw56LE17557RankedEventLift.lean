import Raw56LE17557EventSubstitution
import Raw56LE17557FrameMachine

/-!
  A rank-refinement of the entire parameterized 17557 triad substitution.
  All normal-A triads are automatically born at rank 0 with second
  right one-run 13 = 2^4-3, and each substituted normal A increases rank
  by one (b -> 2b+3). This is the exact rank index used by Agent 1's
  source-accepted finite-frame safety theorem.

  The theorem is an abstract *event grammar* erasure equality. The
  source-Turing-machine all-epoch synchronization remains open.
-/

namespace BB6.Agent4Raw56LE17557RankedEventLift
open BB6.Agent4Raw56LE17557TimeCocycle
open BB6.Agent4Raw56LE17557EventSubstitution
open BB6.Agent1Raw56.LE17557FrameSchedule
open BB6.Agent1Raw56.LE17557FrameMachine

inductive RankedTriad
  | normal (a c r : Nat) (last : Bool)
  | carry (a c d : Nat) (last : Bool)
  | b (a b : Nat) (last : Bool)
  deriving Repr, DecidableEq

def erase : RankedTriad → Triad
  | .normal a c r last => .aNormal a (normalB r) c last
  | .carry a c d last => .aCarry a c d last
  | .b a b last => .b a b last

def lift : RankedTriad → List RankedTriad
  | .normal a c r last =>
      let ch := 2*c + lastBit last
      [.normal (2*a+2) ch (r+1) last,
       .b 2 (ch+5) last,
       .carry 2 (ch+8) 0 last]
  | .carry a c d last =>
      let ch := 2*c + lastBit last
      [.normal (2*a+2) ch 0 last,
       .b 2 (ch+5) last,
       .carry 2 (ch+8) (2*a+2*d+4) last]
  | .b a b last =>
      [.b (2*a+2) (2*b+3+lastBit last) last,
       .b 2 5 false,
       .carry 2 8 0 false]

def liftWord (xs : List RankedTriad) : List RankedTriad :=
  xs.flatMap lift

/-- Erasure preserves the full descriptor lift. Normal A rank transport
    is the exact normalB recurrence, not a numerical coincidence. -/
theorem erase_lift (e : RankedTriad) :
    (lift e).map erase = expand (erase e) := by
  cases e with
  | normal a c r last =>
      simp [lift, erase, expand, normalB_succ]
  | carry a c d last =>
      simp [lift, erase, expand, normalB_zero]
  | b a b last =>
      rfl

theorem erase_liftWord (xs : List RankedTriad) :
    (liftWord xs).map erase = expandWord (xs.map erase) := by
  induction xs with
  | nil => rfl
  | cons e es ih =>
      change ((lift e ++ liftWord es).map erase) =
        expand (erase e) ++ expandWord (es.map erase)
      rw [List.map_append, erase_lift, ih]

def rankedBase : List RankedTriad :=
  [.carry 2 7 0 true,
   .b 6 12 true, .b 2 5 false,
   .carry 2 8 0 false]

theorem erase_base :
    rankedBase.map erase = baseEvents := by decide

def rankedEpochs : Nat → List RankedTriad
  | 0 => rankedBase
  | n+1 => liftWord (rankedEpochs n)

/-- Every normal-A event of the rank-refined grammar has exactly the
    source-approved frame index r, and erasure is correct for all ranks. -/
theorem erase_rankedEpochs (n : Nat) :
    (rankedEpochs n).map erase = epochs n := by
  induction n with
  | zero => exact erase_base
  | succ n ih =>
      change (liftWord (rankedEpochs n)).map erase =
        expandWord (epochs n)
      rw [erase_liftWord, ih]

/-- Hence every normal-A descriptor's physical second one-run is a
    legal ranked normal source parameter with the exact finite-frame
    low-runway length used by Agent 1's accepted stack theorem. -/
theorem normal_runway_rank (a c r : Nat) (last : Bool) :
    let e := erase (.normal a c r last)
    (match e with
      | .aNormal _ b _ _ => b
      | _ => 0) =
    lowCost (frame r) + 6 := by
  simp [erase]
  have h := normal_push_eq_frame_cost r
  have hge := normalB_ge6 r
  omega

theorem normal_runway_mod8 (a c r : Nat) (last : Bool) :
    let e := erase (.normal a c r last)
    (match e with
      | .aNormal _ b _ _ => b
      | _ => 0) % 8 = 5 := by
  simpa [erase] using normalB_mod8 r

#print axioms erase_lift
#print axioms erase_liftWord
#print axioms erase_rankedEpochs
#print axioms normal_runway_rank
#print axioms normal_runway_mod8
end BB6.Agent4Raw56LE17557RankedEventLift
