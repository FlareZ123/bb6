import NineteenthBlock3
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.DRegularFastSmall

open DRegular BB6.DRegularFast

/-- A parameterized block evaluator using canonical-base reduction and the
    exact 3-adic shift after each block. -/
def fastRunBlocksWith (B : Nat) : Nat → L → Option L
  | 0, s => some s
  | n+1, s =>
      match run B (baseState s B) with
      | none => none
      | some t => fastRunBlocksWith B n
          (BB6.DRegularShift.shiftNat t (8^B * liftParam s B))

/-- Correctness with a residual tail, proved by induction on the number of
    blocks rather than induction on the total number of source steps. -/
theorem run_blockedWith (B n r : Nat) : ∀ s : L, Canon s →
    run (B*n+r) s = (fastRunBlocksWith B n s).bind (run r) := by
  induction n with
  | zero =>
      intro s hs
      simp [fastRunBlocksWith, run]
  | succ n ih =>
      intro s hs
      have hmul : B*(n+1)+r = B+(B*n+r) := by
        rw [Nat.mul_succ]
        omega
      rw [hmul, BB6.DRegularFast.run_add]
      rw [BB6.DRegularFast.run_block s B hs]
      cases h : run B (baseState s B) with
      | none => simp [fastRunBlocksWith, h]
      | some t =>
          let t' := BB6.DRegularShift.shiftNat t (8^B * liftParam s B)
          have hrun : run B s = some t' := by
            rw [BB6.DRegularFast.run_block s B hs, h]
            rfl
          have hcanon : Canon t' := BB6.DRegularFast.run_canon B s t' hs hrun
          have ih' := ih t' hcanon
          simpa [fastRunBlocksWith, h, t', Option.bind_assoc] using ih'

/-- Split a sequence of blocks into consecutive groups. -/
theorem fastRunBlocksWith_add (B n m : Nat) :
    ∀ s, fastRunBlocksWith B (n+m) s =
      (fastRunBlocksWith B n s).bind (fun t => fastRunBlocksWith B m t) := by
  induction n with
  | zero =>
      intro s
      simp [fastRunBlocksWith]
  | succ n ih =>
      intro s
      simp only [Nat.succ_add, fastRunBlocksWith]
      cases h : run B (baseState s B) with
      | none => simp [h]
      | some t => simp [h, ih]

#print axioms run_blockedWith
#print axioms fastRunBlocksWith_add

end BB6.DRegularFastSmall
