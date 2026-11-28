import Raw56LE17557FrameSchedule
import Raw56LE17557EpisodeWord

namespace BB6.Agent1Raw56.LE17557ActionGrammar
open BB6.Agent1Raw56.LE17557EpisodeWord

/-- Rank-labelled macro actions.  `normal r` creates a rank-r finite
    zero-run frame, `b` is a B triad, and `carry` is the b=5 A triad. -/
inductive Action where
  | normal : Nat → Action
  | b : Action
  | carry : Action
  deriving DecidableEq, Repr

/-- Forget action refinement and recover the ordinary A/B triad letter. -/
def erase : Action → Bool
  | .normal _ => false
  | .b => true
  | .carry => false

/-- One level of the observed rank-labelled lift. -/
def liftLetter : Action → List Action
  | .normal r => [.normal (r+1), .b, .carry]
  | .b => [.b, .b, .carry]
  | .carry => [.normal 0, .b, .carry]

def lift (w : List Action) : List Action := w.flatMap liftLetter
def eraseWord (w : List Action) : List Bool := w.map erase

@[simp] theorem erase_liftLetter (a : Action) :
    eraseWord (liftLetter a) = substLetter (erase a) := by
  cases a <;> simp [liftLetter, eraseWord, erase, substLetter]

@[simp] theorem lift_nil : lift [] = [] := rfl
@[simp] theorem lift_cons (a : Action) (w : List Action) :
    lift (a::w) = liftLetter a ++ lift w := rfl

@[simp] theorem eraseWord_append (u v : List Action) :
    eraseWord (u++v) = eraseWord u ++ eraseWord v := by
  simp [eraseWord]

/-- The rank-labelled lift is exactly a refinement of the existing ternary
    substitution sigma after erasing N/C back to A. -/
theorem erase_lift (w : List Action) :
    eraseWord (lift w) = subst (eraseWord w) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [lift_cons, eraseWord_append, erase_liftLetter, ih]
      rfl

/-- Epoch 2 action classification, then repeated rank-labelled lifting. -/
def actionEpoch : Nat → List Action
  | 0 => [.carry, .b, .b, .carry]
  | n+1 => lift (actionEpoch n)

/-- The same epochs after forgetting the N/C refinement. -/
def macroEpoch : Nat → List Bool
  | 0 => [false, true, true, false]
  | n+1 => subst (macroEpoch n)

theorem erase_actionEpoch (n : Nat) :
    eraseWord (actionEpoch n) = macroEpoch n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [actionEpoch, erase_lift, ih]
      rfl

@[simp] theorem liftLetter_length (a : Action) :
    (liftLetter a).length = 3 := by
  cases a <;> rfl

theorem lift_length (w : List Action) :
    (lift w).length = 3*w.length := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [lift_cons, List.length_append, liftLetter_length, ih]
      simp
      omega

theorem actionEpoch_length (n : Nat) :
    (actionEpoch n).length = 4*3^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [actionEpoch, lift_length, ih]
      simp [Nat.pow_succ]
      omega

/-- A canonical rank-r frame segment is the r-fold lift of N_0 B. -/
def segment : Nat → List Action
  | 0 => [.normal 0, .b]
  | r+1 => lift (segment r)

theorem segment_length (r : Nat) :
    (segment r).length = 2*3^r := by
  induction r with
  | zero => decide
  | succ r ih =>
      rw [segment, lift_length, ih]
      simp [Nat.pow_succ]
      omega

/-- The lifted segment advertises its rank in its first normal action. -/
theorem segment_head (r : Nat) :
    (segment r).head? = some (.normal r) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      cases h : segment r with
      | nil => simp [h] at ih
      | cons a w =>
          have ha : a = .normal r := by
            simpa [h] using ih
          subst a
          simp [segment, lift, liftLetter, h]

/-- Boolean erasure of the frame segment, starting from AB. -/
def segmentMacro : Nat → List Bool
  | 0 => [false, true]
  | r+1 => subst (segmentMacro r)

theorem erase_segment (r : Nat) :
    eraseWord (segment r) = segmentMacro r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [segment, erase_lift, ih]
      rfl

theorem segmentMacro_length (r : Nat) :
    (segmentMacro r).length = 2*3^r := by
  rw [← erase_segment]
  simp [eraseWord, segment_length]

/-- Body of a rank-r frame after its creating normal action. -/
def body : Nat → List Action
  | 0 => [.b]
  | r+1 => [.b, .carry] ++ lift (body r)

@[simp] theorem lift_append (u v : List Action) :
    lift (u ++ v) = lift u ++ lift v := by
  induction u with
  | nil => rfl
  | cons a u ih =>
      simp [lift, List.append_assoc, ih]

/-- A rank-r segment consists of its creating normal action followed by the
    recursively lifted frame body. -/
theorem segment_eq_normal_body (r : Nat) :
    segment r = .normal r :: body r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [segment, ih]
      simp [lift, liftLetter, body, List.append_assoc]

/-- `OuterTrace xs hs` means that `hs` is the sequence of hits on the
    current outer frame while executing `xs`; complete nested frame segments
    may be skipped as internally closed work. -/
inductive OuterTrace : List Action → List Bool → Prop where
  | nil : OuterTrace [] []
  | hitB {xs hs} : OuterTrace xs hs → OuterTrace (.b :: xs) (true :: hs)
  | hitC {xs hs} : OuterTrace xs hs → OuterTrace (.carry :: xs) (false :: hs)
  | skip (r : Nat) {xs hs} :
      OuterTrace xs hs → OuterTrace (segment r ++ xs) hs

/-- Lifting a macro word refines each outer B into B B C, while an outer carry
    remains C because the inserted N_0 B pair is a complete nested rank-0
    frame.  Existing nested frames simply promote by one rank. -/
theorem outerTrace_lift {xs hs : List _} (h : OuterTrace xs hs) :
    OuterTrace (lift xs)
      (BB6.Agent1Raw56.LE17557FrameSchedule.refine hs) := by
  induction h with
  | nil => exact .nil
  | hitB h ih =>
      simpa [lift, liftLetter,
        BB6.Agent1Raw56.LE17557FrameSchedule.refine,
        BB6.Agent1Raw56.LE17557FrameSchedule.refineLetter] using
        OuterTrace.hitB (OuterTrace.hitB (OuterTrace.hitC ih))
  | hitC h ih =>
      have hc : OuterTrace
          (.carry :: lift _)
          (false :: BB6.Agent1Raw56.LE17557FrameSchedule.refine _) :=
        OuterTrace.hitC ih
      have hs := OuterTrace.skip 0 hc
      simpa [segment, lift, liftLetter,
        BB6.Agent1Raw56.LE17557FrameSchedule.refine,
        BB6.Agent1Raw56.LE17557FrameSchedule.refineLetter,
        List.append_assoc] using hs
  | skip r h ih =>
      have hs := OuterTrace.skip (r+1) ih
      simpa [lift_append, segment] using hs

/-- The body of every rank-r segment has exactly the recursively derived frame
    hit schedule.  This is the syntactic nesting theorem missing from the
    earlier finite replay: nested frames are closed structurally rather than
    by a bounded scan. -/
theorem body_outerTrace (r : Nat) :
    OuterTrace (body r) (BB6.Agent1Raw56.LE17557FrameSchedule.frame r) := by
  induction r with
  | zero =>
      exact OuterTrace.hitB OuterTrace.nil
  | succ r ih =>
      have hl := outerTrace_lift ih
      have hbc := OuterTrace.hitB (OuterTrace.hitC hl)
      simpa [body,
        BB6.Agent1Raw56.LE17557FrameSchedule.frame,
        BB6.Agent1Raw56.LE17557FrameSchedule.frame_succ_refine] using hbc

/-- Consequently a complete rank-r segment is one nested frame followed by no
    outer-frame hit at all. -/
theorem segment_is_closed_nested (r : Nat) :
    OuterTrace (segment r) [] := by
  have h : OuterTrace [] [] := OuterTrace.nil
  simpa using OuterTrace.skip r h

/-- Rank-bounded version of `OuterTrace`.  At ambient rank k, only complete
    nested frames of strictly smaller rank may be skipped.  This removes the
    circularity from the unbounded syntactic trace relation. -/
inductive OuterTraceBelow (k : Nat) : List Action → List Bool → Prop where
  | nil : OuterTraceBelow k [] []
  | hitB {xs hs} :
      OuterTraceBelow k xs hs →
      OuterTraceBelow k (.b :: xs) (true :: hs)
  | hitC {xs hs} :
      OuterTraceBelow k xs hs →
      OuterTraceBelow k (.carry :: xs) (false :: hs)
  | skip {r : Nat} (hr : r < k) {xs hs} :
      OuterTraceBelow k xs hs →
      OuterTraceBelow k (segment r ++ xs) hs

/-- Lifting preserves the strict nesting discipline: an old nested rank r
    becomes r+1, while the new frame inserted by a lifted carry has rank 0. -/
theorem outerTraceBelow_lift {k : Nat} {xs hs : List _}
    (h : OuterTraceBelow k xs hs) :
    OuterTraceBelow (k+1) (lift xs)
      (BB6.Agent1Raw56.LE17557FrameSchedule.refine hs) := by
  induction h with
  | nil => exact .nil
  | hitB h ih =>
      simpa [lift, liftLetter,
        BB6.Agent1Raw56.LE17557FrameSchedule.refine,
        BB6.Agent1Raw56.LE17557FrameSchedule.refineLetter] using
        OuterTraceBelow.hitB (OuterTraceBelow.hitB (OuterTraceBelow.hitC ih))
  | hitC h ih =>
      have hc : OuterTraceBelow (k+1)
          (.carry :: lift _)
          (false :: BB6.Agent1Raw56.LE17557FrameSchedule.refine _) :=
        OuterTraceBelow.hitC ih
      have hs := OuterTraceBelow.skip (k := k+1) (r := 0) (Nat.zero_lt_succ k) hc
      simpa [segment, lift, liftLetter,
        BB6.Agent1Raw56.LE17557FrameSchedule.refine,
        BB6.Agent1Raw56.LE17557FrameSchedule.refineLetter,
        List.append_assoc] using hs
  | @skip r hr xs hs h ih =>
      have hs' := OuterTraceBelow.skip (k := k+1) (r := r+1)
        (Nat.succ_lt_succ hr) ih
      simpa [lift_append, segment] using hs'

/-- A rank-r body contains only strictly lower-rank nested frames.  Its outer
    hit sequence is still exactly F_r. -/
theorem body_outerTraceBelow (r : Nat) :
    OuterTraceBelow r (body r)
      (BB6.Agent1Raw56.LE17557FrameSchedule.frame r) := by
  induction r with
  | zero =>
      exact OuterTraceBelow.hitB OuterTraceBelow.nil
  | succ r ih =>
      have hl := outerTraceBelow_lift ih
      have hbc := OuterTraceBelow.hitB (OuterTraceBelow.hitC hl)
      simpa [body,
        BB6.Agent1Raw56.LE17557FrameSchedule.frame,
        BB6.Agent1Raw56.LE17557FrameSchedule.frame_succ_refine] using hbc

/-- Forgetting the rank bound recovers the earlier outer trace. -/
theorem outerTraceBelow_forget {k : Nat} {xs hs : List _}
    (h : OuterTraceBelow k xs hs) : OuterTrace xs hs := by
  induction h with
  | nil => exact .nil
  | hitB h ih => exact OuterTrace.hitB ih
  | hitC h ih => exact OuterTrace.hitC ih
  | skip hr h ih => exact OuterTrace.skip _ ih

#print axioms erase_lift
#print axioms erase_actionEpoch
#print axioms actionEpoch_length
#print axioms segment_length
#print axioms segment_head
#print axioms segment_eq_normal_body
#print axioms outerTrace_lift
#print axioms body_outerTrace
#print axioms segment_is_closed_nested
#print axioms outerTraceBelow_lift
#print axioms body_outerTraceBelow
#print axioms outerTraceBelow_forget
#print axioms erase_segment

end BB6.Agent1Raw56.LE17557ActionGrammar
