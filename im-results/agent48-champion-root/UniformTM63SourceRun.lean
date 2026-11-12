import S0UniformBridge
import UniformTM63HeadOffset
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
      simp [uniformTapeAt, hnot, hcoord, moveL_right_zero, sideBit]
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

/-- A single total zipper step is exactly one original TM63 primitive move,
provided the current query is not the undefined A/1 halt. -/
theorem uniformStep_rawStep (c : TM63Uniform.Cfg) (h : Int)
    (hc : c.st < 6) (hsafe : ¬ (c.st = 0 ∧ c.h = true)) :
    BB6Coverage.rawStep tm2 (uniformConfigAt h c hc) =
      some (uniformConfigAt (h + headDelta c) (TM63Uniform.step c)
        (step_state_lt c hc)) := by
  cases c with
  | mk q l b r =>
    have hs : ¬ (q = 0 ∧ b = true) := hsafe
    cases q with
    | zero =>
      cases b with
      | false =>
          simp [TM63Uniform.step, headDelta, uniformConfigAt, tm2,
            BB6Coverage.rawStep, BB6Coverage.readSlot, BB6Coverage.applyMove,
            uniformTapeAt_head, uniformTapeAt_moveR, moveR_st, moveL_st]
      | true => exact False.elim (hs ⟨rfl, rfl⟩)
    | succ q =>
      cases q with
      | zero =>
        cases b <;> simp [TM63Uniform.step, headDelta, uniformConfigAt, tm2,
          BB6Coverage.rawStep, BB6Coverage.readSlot, BB6Coverage.applyMove,
          uniformTapeAt_head, uniformTapeAt_moveR, uniformTapeAt_moveL,
          moveR_st, moveL_st]
      | succ q =>
        cases q with
        | zero =>
          cases b <;> simp [TM63Uniform.step, headDelta, uniformConfigAt, tm2,
            BB6Coverage.rawStep, BB6Coverage.readSlot, BB6Coverage.applyMove,
            uniformTapeAt_head, uniformTapeAt_moveR, uniformTapeAt_moveL,
            moveR_st, moveL_st]
        | succ q =>
          cases q with
          | zero =>
            cases b <;> simp [TM63Uniform.step, headDelta, uniformConfigAt, tm2,
              BB6Coverage.rawStep, BB6Coverage.readSlot, BB6Coverage.applyMove,
              uniformTapeAt_head, uniformTapeAt_moveR, uniformTapeAt_moveL,
              moveR_st, moveL_st]
          | succ q =>
            cases q with
            | zero =>
              cases b <;> simp [TM63Uniform.step, headDelta, uniformConfigAt, tm2,
                BB6Coverage.rawStep, BB6Coverage.readSlot, BB6Coverage.applyMove,
                uniformTapeAt_head, uniformTapeAt_moveR, uniformTapeAt_moveL,
                moveR_st, moveL_st]
            | succ q =>
              cases q with
              | zero =>
                cases b <;> simp [TM63Uniform.step, headDelta, uniformConfigAt, tm2,
                  BB6Coverage.rawStep, BB6Coverage.readSlot, BB6Coverage.applyMove,
                  uniformTapeAt_head, uniformTapeAt_moveR, uniformTapeAt_moveL,
                  moveR_st, moveL_st]
              | succ q => omega

/-- Validity of the state component is invariant under the total zipper run. -/
theorem run_state_lt (n : Nat) (c : TM63Uniform.Cfg) (hc : c.st < 6) :
    (TM63Uniform.run n c).st < 6 := by
  induction n generalizing c with
  | zero => exact hc
  | succ n ih => exact ih (TM63Uniform.step c) (step_state_lt c hc)

/-- Transport a safe finite zipper run to the original infinite-tape
semantics, preserving the exact accumulated physical head displacement. -/
theorem run_uniform_source (n : Nat) (c : TM63Uniform.Cfg) (h : Int)
    (hc : c.st < 6)
    (hsafe : ∀ t, t ≤ n →
      ¬ ((TM63Uniform.run t c).st = 0 ∧ (TM63Uniform.run t c).h = true)) :
    BB6Coverage.run tm2 n (uniformConfigAt h c hc) =
      some (uniformConfigAt (h + headOffset n c) (TM63Uniform.run n c)
        (run_state_lt n c hc)) := by
  induction n generalizing c h hc with
  | zero =>
      simp [BB6Coverage.run, TM63Uniform.run, headOffset, uniformConfigAt]
  | succ n ih =>
      have hsafeN := hsafe n (by omega)
      have hcN := run_state_lt n c hc
      have hIH := ih c h hc (fun t ht => hsafe t (by omega))
      have hstep := uniformStep_rawStep (TM63Uniform.run n c)
        (h + headOffset n c) hcN hsafeN
      have hrun : TM63Uniform.run (n + 1) c =
          TM63Uniform.step (TM63Uniform.run n c) := by
        simpa [TM63Uniform.run] using (TM63Uniform.run_add n 1 c)
      have hoff : headOffset (n + 1) c =
          headOffset n c + headDelta (TM63Uniform.run n c) := by
        simpa [headOffset] using (headOffset_add n 1 c)
      change (BB6Coverage.run tm2 n (uniformConfigAt h c hc)).bind
          (BB6Coverage.rawStep tm2) = _
      rw [hIH]
      simp only [Option.bind_some]
      rw [hstep]
      have hcfg :
          uniformConfigAt (h + headOffset n c + headDelta (TM63Uniform.run n c))
              (TM63Uniform.step (TM63Uniform.run n c))
              (step_state_lt (TM63Uniform.run n c) hcN) =
            uniformConfigAt (h + headOffset (n + 1) c)
              (TM63Uniform.run (n + 1) c) (run_state_lt (n + 1) c hc) := by
        simp [hrun, hoff, uniformConfigAt, Int.add_assoc]
      exact congrArg some hcfg

#print axioms uniformStep_rawStep
#print axioms run_uniform_source

end BB6Coverage.Agent48UniformRun
