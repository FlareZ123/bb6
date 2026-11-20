import NineteenthBlock3
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2NineteenthRoot

open DRegular BB6.DRegularFast

/-- Composition law for the 3-adic 512-section evaluator. -/
theorem fastRunBlocks_add (m n : Nat) :
    ∀ s : L,
      fastRunBlocks (m+n) s =
        (fastRunBlocks m s).bind (fastRunBlocks n) := by
  induction m with
  | zero =>
      intro s
      simp [fastRunBlocks]
  | succ m ih =>
      intro s
      simp only [Nat.succ_add, fastRunBlocks]
      cases hr : run blockSize (baseState s blockSize) with
      | none =>
          simp [hr]
      | some t =>
          let t' := shiftNat t (8^blockSize * liftParam s blockSize)
          simpa [hr, t'] using ih t'

/-- Exactness for full 512-section blocks followed by an arbitrary
    remainder.  The induction composes one 512-step block at a time,
    avoiding a single large run_add induction. -/
theorem fastRunBlocks_tail_correct (n : Nat) :
    ∀ (r : Nat) (s : L), Canon s →
      run (blockSize*n + r) s =
        (fastRunBlocks n s).bind (run r) := by
  induction n with
  | zero =>
      intro r s hs
      simp [fastRunBlocks, run]
  | succ n ih =>
      intro r s hs
      let base := baseState s blockSize
      let p := liftParam s blockSize
      have hmul : blockSize*(n+1)+r = blockSize + (blockSize*n+r) := by
        simp [blockSize, Nat.mul_add]
        omega
      have hblock := run_block s blockSize hs
      rw [hmul, run_add, hblock]
      cases hr : run blockSize base with
      | none =>
          simp [fastRunBlocks, base, hr]
      | some t =>
          let t' := shiftNat t (8^blockSize*p)
          have hb : run blockSize s = some t' := by
            rw [hblock, hr]
            rfl
          have ht' : Canon t' := run_canon blockSize s t' hs hb
          have hright : fastRunBlocks (n+1) s = fastRunBlocks n t' := by
            simp [fastRunBlocks, base, p, hr, t']
          rw [hright]
          exact ih r t' ht'

/-- The first two exact 4,096-section checkpoints are eight 512-blocks
    each, as witnessed by the already checked fast evaluator. -/
theorem block19_1_blocks_exact :
    fastRunBlocks 8 seed19 = some block19_1 := by
  have h := fastRunBlocks_correct 8 seed19 seed19_canon
  have hrun : run 4096 seed19 = fastRunBlocks 8 seed19 := by
    simpa [blockSize] using h
  rw [block19_1_exact] at hrun
  exact hrun.symm

theorem block19_2_blocks_exact :
    fastRunBlocks 8 block19_1 = some block19_2 := by
  have h := fastRunBlocks_correct 8 block19_1 block19_1_canon
  have hrun : run 4096 block19_1 = fastRunBlocks 8 block19_1 := by
    simpa [blockSize] using h
  rw [block19_2_exact] at hrun
  exact hrun.symm

theorem blocks19_1_to_11 :
    fastRunBlocks 11 block19_1 = fastRunBlocks 3 block19_2 := by
  have h := fastRunBlocks_add 8 3 block19_1
  rw [block19_2_blocks_exact] at h
  simpa using h

theorem blocks19_from_seed_exact :
    fastRunBlocks 19 seed19 = fastRunBlocks 3 block19_2 := by
  have h := fastRunBlocks_add 8 11 seed19
  rw [block19_1_blocks_exact, blocks19_1_to_11] at h
  simpa using h

theorem final52_exact :
    (fastRunBlocks 3 block19_2).bind (run 52) =
      some ⟨9*t19+10,9,1⟩ := by
  have h := fastRunBlocks_tail_correct 3 52 block19_2 block19_2_canon
  have hlen : blockSize*3+52 = 1588 := by norm_num [blockSize]
  have hrun :
      run 1588 block19_2 =
        (fastRunBlocks 3 block19_2).bind (run 52) := by
    simpa [hlen] using h
  rw [terminal1588_exact] at hrun
  exact hrun.symm

theorem tail5684_exact :
    run 5684 block19_1 = some ⟨9*t19+10,9,1⟩ := by
  have h := fastRunBlocks_tail_correct 11 52 block19_1 block19_1_canon
  have hlen : blockSize*11+52 = 5684 := by norm_num [blockSize]
  have hrun :
      run 5684 block19_1 =
        (fastRunBlocks 11 block19_1).bind (run 52) := by
    simpa [hlen] using h
  rw [blocks19_1_to_11, final52_exact] at hrun
  exact hrun

end BB6.Agent2NineteenthRoot
