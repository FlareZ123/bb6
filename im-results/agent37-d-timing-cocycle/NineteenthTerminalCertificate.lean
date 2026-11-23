import NineteenthBlock3
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.DRegularFastSmall

open DRegular BB6.DRegularFast

/-- A parameterized block evaluator using the same canonical-base and
    3-adic shift decomposition as `DRegularFast.fastRunBlocks`. -/
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

end BB6.DRegularFastSmall

namespace BB6.Agent2NineteenthRoot

open DRegular BB6.DRegularFast BB6.DRegularFastSmall

/-- Kernel-only exact 5,684-section tail. The generic 64-step block
    evaluator reduces the computation to 88 blocks and a 52-step remainder;
    `decide` checks the resulting finite computation in the kernel. -/
theorem tail5684_exact :
    run 5684 block19_1 = some ⟨9*t19+10,9,1⟩ := by
  have hlen : 5684 = 64*88+52 := by decide
  rw [hlen]
  rw [run_blockedWith 64 88 52 block19_1 block19_1_canon]
  decide

/-- Compose the 4,096-step prefix and the 5,684-step tail using the same
    64-step block evaluator. This deliberately avoids importing the large
    tail object into a second Lean process: the tail and final endpoint are
    checked together in one kernel invocation. -/
theorem terminal9780_exact :
    run 9780 seed19 = some ⟨9*t19+10,9,1⟩ := by
  have hlen : 9780 = 512*8+5684 := by decide
  rw [hlen]
  rw [run_blockedWith 512 8 5684 seed19 seed19_canon]
  have hfast : fastRunBlocksWith 512 8 seed19 = some block19_1 := by
    have h := run_blockedWith 512 8 0 seed19 seed19_canon
    have hlen0 : 512*8+0 = 4096 := by decide
    rw [hlen0, block19_1_exact] at h
    simpa [run] using h
  rw [hfast]
  exact tail5684_exact

theorem t19_mod27_exact : t19 % 27 = 12 :=
  t19_mod27

#print axioms tail5684_exact
#print axioms terminal9780_exact
#print axioms t19_mod27_exact

end BB6.Agent2NineteenthRoot
