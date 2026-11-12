import S0UniformBridge
import UniformTM63HeadOffset
import TerminalChampion
import Lean.Elab.Tactic.Omega

/-!
# Source transport for the all-valuation TM63 zipper

The finite zipper uses nearest-first left/right lists and totalizes the
undefined A/1 query by freezing.  This module embeds every valid zipper
configuration into the original bi-infinite-tape Config, proves exact
one-step correspondence away from A/1, and transports finite safe runs while
tracking the signed physical head displacement.
-/

namespace BB6Coverage.Agent48UniformRun

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent48UniformBridge
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent48UniformHeadOffset
open BB6Coverage.TerminalBridge
open TM63Uniform

/-- Embed any valid finite zipper state at an absolute physical head. -/
def uniformConfigAt (h : Int) (c : TM63Uniform.Cfg) (hc : c.st < 6) : Config :=
  ⟨⟨c.st, hc⟩, h, uniformTapeAt c h⟩

@[simp] theorem uniformTapeAt_head (c : TM63Uniform.Cfg) (h : Int) :
    uniformTapeAt c h h = c.h := by
  simp [uniformTapeAt, sideBit]

private theorem toNat_add_one (z : Int) (hz : 0 ≤ z) :
    Int.toNat (z + 1) = Int.toNat z + 1 := by
  have hz' : 0 ≤ z + 1 := by omega
  have h1 : (Int.toNat (z + 1) : Int) = z + 1 :=
    Int.toNat_of_nonneg hz'
  have h0 : (Int.toNat z : Int) = z :=
    Int.toNat_of_nonneg hz
  omega

private theorem toNat_sub_one (z : Int) (hz : 1 ≤ z) :
    Int.toNat (z - 1) + 1 = Int.toNat z := by
  have hz' : 0 ≤ z - 1 := by omega
  have h1 : (Int.toNat (z - 1) : Int) = z - 1 :=
    Int.toNat_of_nonneg hz'
  have h0 : (Int.toNat z : Int) = z :=
    Int.toNat_of_nonneg (by omega)
  omega

private theorem write_true (h : Int) (t : Int → Bool) :
    (fun x => if x = h then true else t x) =
      (fun x => decide (x = h) || t x) := by
  funext x
  by_cases hx : x = h <;> simp [hx]

private theorem write_false (h : Int) (t : Int → Bool) :
    (fun x => if x = h then false else t x) =
      (fun x => ! decide (x = h) && t x) := by
  funext x
  by_cases hx : x = h <;> simp [hx]

private theorem terminalSet_true (t : Int → Bool) (h : Int) :
    TerminalFinish.set t h true =
      (fun x => decide (x = h) || t x) := by
  funext x
  by_cases hx : x = h <;> simp [TerminalFinish.set, hx]

private theorem terminalSet_false (t : Int → Bool) (h : Int) :
    TerminalFinish.set t h false =
      (fun x => ! decide (x = h) && t x) := by
  funext x
  by_cases hx : x = h <;> simp [TerminalFinish.set, hx]

private theorem moveR_left (c : TM63Uniform.Cfg) (b : Bool) (s n : Nat) :
    sideBit ((TM63Uniform.moveR c b s).h :: (TM63Uniform.moveR c b s).l)
      (n + 1) = sideBit (b :: c.l) n := by
  cases c with
  | mk q l h r => cases r <;> rfl

private theorem moveR_head (c : TM63Uniform.Cfg) (b : Bool) (s : Nat) :
    (TM63Uniform.moveR c b s).h = sideBit c.r 0 := by
  cases c with
  | mk q l h r => cases r <;> rfl

private theorem moveR_right (c : TM63Uniform.Cfg) (b : Bool) (s n : Nat) :
    sideBit (TM63Uniform.moveR c b s).r n = sideBit c.r (n + 1) := by
  cases c with
  | mk q l h r => cases r <;> rfl

private theorem moveR_st (c : TM63Uniform.Cfg) (b : Bool) (s : Nat) :
    (TM63Uniform.moveR c b s).st = s := by
  cases c with
  | mk q l h r => cases r <;> rfl

private theorem moveL_left (c : TM63Uniform.Cfg) (b : Bool) (s n : Nat) :
    sideBit ((TM63Uniform.moveL c b s).h :: (TM63Uniform.moveL c b s).l) n =
      sideBit (c.h :: c.l) (n + 1) := by
  cases c with
  | mk q l h r => cases l <;> cases n <;> rfl

private theorem moveL_right (c : TM63Uniform.Cfg) (b : Bool) (s n : Nat) :
    sideBit (TM63Uniform.moveL c b s).r (n + 1) = sideBit c.r n := by
  cases c with
  | mk q l h r => cases l <;> rfl

private theorem moveL_right_zero (c : TM63Uniform.Cfg) (b : Bool) (s : Nat) :
    sideBit (TM63Uniform.moveL c b s).r 0 = b := by
  cases c with
  | mk q l h r => cases l <;> rfl

private theorem moveL_st (c : TM63Uniform.Cfg) (b : Bool) (s : Nat) :
    (TM63Uniform.moveL c b s).st = s := by
  cases c with
  | mk q l h r => cases l <;> rfl

/-- Moving the zipper head right corresponds to writing at the old head and
moving the physical head one cell right. -/
theorem uniformTapeAt_moveR (c : TM63Uniform.Cfg) (h : Int)
    (b : Bool) (s : Nat) :
    uniformTapeAt (TM63Uniform.moveR c b s) (h + 1) =
      (fun x => if x = h then b else uniformTapeAt c h x) := by
  funext x
  by_cases hx : x ≤ h
  · have hx' : x ≤ h + 1 := by omega
    have hidx : Int.toNat (h + 1 - x) = Int.toNat (h - x) + 1 := by
      rw [show h + 1 - x = (h - x) + 1 by omega]
      exact toNat_add_one (h - x) (by omega)
    by_cases heq : x = h
    · subst x
      have hcoord : h + 1 - h = 1 := by omega
      simp [uniformTapeAt, hcoord, hx', moveR_left, sideBit]
    · have hn : Int.toNat (h - x) ≠ 0 := by
        intro hz
        have hcast : (Int.toNat (h - x) : Int) = h - x :=
          Int.toNat_of_nonneg (by omega)
        simp [hz] at hcast
        omega
      simp only [uniformTapeAt, if_pos hx, if_pos hx']
      rw [hidx, moveR_left]
      simp only [if_neg heq]
      cases hn' : Int.toNat (h - x) with
      | zero => exact False.elim (hn hn')
      | succ n => simp [sideBit]
  · by_cases hx' : x ≤ h + 1
    · have heq : x = h + 1 := by omega
      subst x
      have hcoord : h + 1 - h = 1 := by omega
      have hne : h + 1 ≠ h := by omega
      simp [uniformTapeAt, hx, hx', hcoord, hne, moveR_head, sideBit]
    · have hidx : Int.toNat (x - (h + 1) - 1) + 1 =
          Int.toNat (x - h - 1) := by
        have heq : x - (h + 1) - 1 = (x - h - 1) - 1 := by omega
        rw [heq]
        exact toNat_sub_one (x - h - 1) (by omega)
      have hne : x ≠ h := by omega
      simp only [uniformTapeAt, if_neg hx, if_neg hx']
      rw [moveR_right, hidx]
      simp [hne]

/-- Moving the zipper head left corresponds to writing at the old head and
moving the physical head one cell left. -/
theorem uniformTapeAt_moveL (c : TM63Uniform.Cfg) (h : Int)
    (b : Bool) (s : Nat) :
    uniformTapeAt (TM63Uniform.moveL c b s) (h - 1) =
      (fun x => if x = h then b else uniformTapeAt c h x) := by
  funext x
  by_cases hx : x < h
  · have hxL : x ≤ h - 1 := by omega
    have hxR : x ≤ h := by omega
    have hidx : Int.toNat (h - 1 - x) + 1 = Int.toNat (h - x) := by
      have heq : h - 1 - x = (h - x) - 1 := by omega
      rw [heq]
      exact toNat_sub_one (h - x) (by omega)
    simp only [uniformTapeAt, if_pos hxL, if_pos hxR]
    rw [moveL_left, hidx]
    have hne : x ≠ h := by omega
    simp [hne]
  · by_cases heq : x = h
    · subst x
      have hnot : ¬ h ≤ h - 1 := by omega
      have hcoord : h - (h - 1) = 1 := by omega
      simp only [uniformTapeAt, if_neg hnot]
      rw [hcoord]
      have hzero : Int.toNat (1 - 1) = 0 := by decide
      rw [hzero]
      change sideBit (TM63Uniform.moveL c b s).r 0 = b
      exact moveL_right_zero c b s
    · have hxG : h < x := by omega
      have hnotL : ¬ x ≤ h - 1 := by omega
      have hnotR : ¬ x ≤ h := by omega
      have hidx : Int.toNat (x - (h - 1) - 1) =
          Int.toNat (x - h - 1) + 1 := by
        have heq : x - (h - 1) - 1 = (x - h - 1) + 1 := by omega
        rw [heq]
        exact toNat_add_one (x - h - 1) (by omega)
      simp only [uniformTapeAt, if_neg hnotL, if_neg hnotR]
      rw [hidx, moveL_right]
      simp [heq]

/-- Same left-shift theorem in the additive form used by the source
transition table. -/
theorem uniformTapeAt_moveL_add (c : TM63Uniform.Cfg) (h : Int)
    (b : Bool) (s : Nat) :
    uniformTapeAt (TM63Uniform.moveL c b s) (h + (-1)) =
      (fun x => if x = h then b else uniformTapeAt c h x) := by
  exact uniformTapeAt_moveL c h b s

/-- The total zipper transition preserves the six-state range. -/
theorem step_state_lt (c : TM63Uniform.Cfg) (hc : c.st < 6) :
    (TM63Uniform.step c).st < 6 := by
  cases c with
  | mk q l b r =>
    have hq : q < 6 := hc
    cases q with
    | zero => cases b <;> simp [TM63Uniform.step, moveR_st, moveL_st]
    | succ q =>
      cases q with
      | zero => cases b <;> simp [TM63Uniform.step, moveR_st, moveL_st]
      | succ q =>
        cases q with
        | zero => cases b <;> simp [TM63Uniform.step, moveR_st, moveL_st]
        | succ q =>
          cases q with
          | zero => cases b <;> simp [TM63Uniform.step, moveR_st, moveL_st]
          | succ q =>
            cases q with
            | zero => cases b <;> simp [TM63Uniform.step, moveR_st, moveL_st]
            | succ q =>
              cases q with
              | zero => cases b <;> simp [TM63Uniform.step, moveR_st, moveL_st]
              | succ q => omega

/-- State-preserving map from the uniform zipper to the terminal full-tape
configuration used by the independently verified source bridge. -/
def terminalConfigAt (h : Int) (c : TM63Uniform.Cfg) : TerminalFinish.Conf :=
  ⟨c.st, h, uniformTapeAt c h⟩

/-- One uniform zipper step is exactly one partial terminal-machine step,
away from the unique undefined A/1 query. -/
theorem uniformStep_terminalStep (c : TM63Uniform.Cfg) (h : Int)
    (hc : c.st < 6) (hsafe : ¬ (c.st = 0 ∧ c.h = true)) :
    TerminalFinish.step (terminalConfigAt h c) =
      some (terminalConfigAt (h + headDelta c) (TM63Uniform.step c)) := by
  cases c with
  | mk q l b r =>
    have hq : q < 6 := hc
    have hs : ¬ (q = 0 ∧ b = true) := hsafe
    cases q with
    | zero =>
      cases b with
      | false =>
        simp [TM63Uniform.step, TerminalFinish.step, TerminalFinish.action,
          terminalConfigAt, headDelta, uniformTapeAt_head, uniformTapeAt_moveR,
          moveR_st, moveL_st, terminalSet_true, terminalSet_false]
      | true => exact False.elim (hs ⟨rfl, rfl⟩)
    | succ q =>
      cases q with
      | zero =>
        cases b <;> simp [TM63Uniform.step, TerminalFinish.step, TerminalFinish.action,
          terminalConfigAt, headDelta, uniformTapeAt_head, uniformTapeAt_moveR, uniformTapeAt_moveL_add,
          moveR_st, moveL_st, terminalSet_true, terminalSet_false]
      | succ q =>
        cases q with
        | zero =>
          cases b <;> simp [TM63Uniform.step, TerminalFinish.step, TerminalFinish.action,
            terminalConfigAt, headDelta, uniformTapeAt_head, uniformTapeAt_moveR,
            uniformTapeAt_moveL_add, moveR_st, moveL_st, terminalSet_true, terminalSet_false]
        | succ q =>
          cases q with
          | zero =>
            cases b <;> simp [TM63Uniform.step, TerminalFinish.step, TerminalFinish.action,
              terminalConfigAt, headDelta, uniformTapeAt_head, uniformTapeAt_moveR,
              uniformTapeAt_moveL_add, moveR_st, moveL_st, terminalSet_true, terminalSet_false]
          | succ q =>
            cases q with
            | zero =>
              cases b <;> simp [TM63Uniform.step, TerminalFinish.step, TerminalFinish.action,
                terminalConfigAt, headDelta, uniformTapeAt_head, uniformTapeAt_moveR,
                uniformTapeAt_moveL_add, moveR_st, moveL_st, terminalSet_true, terminalSet_false]
            | succ q =>
              cases q with
              | zero =>
                cases b <;> simp [TM63Uniform.step, TerminalFinish.step, TerminalFinish.action,
                  terminalConfigAt, headDelta, uniformTapeAt_head, uniformTapeAt_moveR,
                  uniformTapeAt_moveL_add, moveR_st, moveL_st, terminalSet_true, terminalSet_false]
              | succ q => omega

/-- Validity of the state component is invariant under the total zipper run. -/
theorem run_state_lt (n : Nat) (c : TM63Uniform.Cfg) (hc : c.st < 6) :
    (TM63Uniform.run n c).st < 6 := by
  induction n generalizing c with
  | zero => exact hc
  | succ n ih => exact ih (TM63Uniform.step c) (step_state_lt c hc)

/-- Transport a safe finite zipper run to the full-tape terminal semantics,
preserving the exact accumulated physical head displacement. -/
theorem run_uniform_terminal (n : Nat) (c : TM63Uniform.Cfg) (h : Int)
    (hc : c.st < 6)
    (hsafe : ∀ t, t ≤ n →
      ¬ ((TM63Uniform.run t c).st = 0 ∧ (TM63Uniform.run t c).h = true)) :
    TerminalFinish.run n (terminalConfigAt h c) =
      some (terminalConfigAt (h + headOffset n c) (TM63Uniform.run n c)) := by
  induction n generalizing c h hc with
  | zero =>
      simp [TerminalFinish.run, terminalConfigAt, TM63Uniform.run, headOffset]
  | succ n ih =>
      have hsafeN := hsafe n (by omega)
      have hcN := run_state_lt n c hc
      have hIH := ih c h hc (fun t ht => hsafe t (by omega))
      have hstep := uniformStep_terminalStep (TM63Uniform.run n c)
        (h + headOffset n c) hcN hsafeN
      have hrun : TM63Uniform.run (n + 1) c =
          TM63Uniform.step (TM63Uniform.run n c) := by
        simpa [TM63Uniform.run] using (TM63Uniform.run_add n 1 c)
      have hoff : headOffset (n + 1) c =
          headOffset n c + headDelta (TM63Uniform.run n c) := by
        simpa [headOffset] using (headOffset_add n 1 c)
      change (TerminalFinish.run n (terminalConfigAt h c)).bind
          TerminalFinish.step = _
      rw [hIH]
      simp only [Option.bind_some]
      rw [hstep]
      have hcfg :
          terminalConfigAt (h + headOffset n c + headDelta (TM63Uniform.run n c))
              (TM63Uniform.step (TM63Uniform.run n c)) =
            terminalConfigAt (h + headOffset (n + 1) c)
              (TM63Uniform.run (n + 1) c) := by
        simp [hrun, hoff, terminalConfigAt, Int.add_assoc]
      exact congrArg some hcfg

/-- The existing terminal embedding is exactly our uniform zipper embedding
whenever the source state is in the six-state range. -/
theorem terminalEmbedAt_eq_uniformConfigAt (h : Int) (c : TM63Uniform.Cfg)
    (hc : c.st < 6) :
    TerminalBridge.embed (terminalConfigAt h c) = uniformConfigAt h c hc := by
  cases c with
  | mk q l b r =>
    simp [TerminalBridge.embed, terminalConfigAt, uniformConfigAt,
      Nat.mod_eq_of_lt hc]

/-- The full source-run transport to the original Agent 48 TM2 machine. -/
theorem run_uniform_source (n : Nat) (c : TM63Uniform.Cfg) (h : Int)
    (hc : c.st < 6)
    (hsafe : ∀ t, t ≤ n →
      ¬ ((TM63Uniform.run t c).st = 0 ∧ (TM63Uniform.run t c).h = true)) :
    BB6Coverage.run tm2 n (uniformConfigAt h c hc) =
      some (uniformConfigAt (h + headOffset n c) (TM63Uniform.run n c)
        (run_state_lt n c hc)) := by
  let tc : TerminalFinish.Conf := terminalConfigAt h c
  have hterm := run_uniform_terminal n c h hc hsafe
  have hbridge := TerminalBridge.run_transport n tc hc
  rw [hterm] at hbridge
  simp only [Option.map_some] at hbridge
  have hstart := terminalEmbedAt_eq_uniformConfigAt h c hc
  have hend := terminalEmbedAt_eq_uniformConfigAt
    (h + headOffset n c) (TM63Uniform.run n c) (run_state_lt n c hc)
  rw [hend, hstart] at hbridge
  rw [TerminalBridge.tm63_eq_tm2] at hbridge
  exact hbridge.symm

#print axioms uniformStep_terminalStep
#print axioms run_uniform_terminal
#print axioms run_uniform_source

end BB6Coverage.Agent48UniformRun
