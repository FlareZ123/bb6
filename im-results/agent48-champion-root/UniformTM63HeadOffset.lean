import UniformTM63
import Lean.Elab.Tactic.Omega

/-!
# Absolute head-displacement accounting for the uniform TM63 zipper

The finite zipper `Cfg` records tape relative to its current head but omits
the absolute head coordinate.  This module adds the exact signed displacement
of each transition and proves local phase offsets.  It is intentionally
separate from the source-TM transport: a Cfg endpoint equality alone does not
establish that the absolute head returned.
-/

namespace BB6Coverage.Agent48UniformHeadOffset

/-- Physical head displacement of one uniform-zipping transition. -/
def headDelta (c : TM63Uniform.Cfg) : Int :=
  if c.st = 0 ∧ c.h = true then 0
  else if (c.st = 1 ∧ c.h = false) ∨
          (c.st = 2 ∧ c.h = true) ∨
          (c.st = 3 ∧ c.h = false) then -1
  else 1

/-- Net physical head displacement during the first n zipper steps. -/
def headOffset : Nat → TM63Uniform.Cfg → Int
  | 0, _ => 0
  | n+1, c => headDelta c + headOffset n (TM63Uniform.step c)

theorem headOffset_add (m n : Nat) (c : TM63Uniform.Cfg) :
    headOffset (m+n) c =
      headOffset m c + headOffset n (TM63Uniform.run m c) := by
  induction m generalizing c with
  | zero => simp [headOffset, TM63Uniform.run]
  | succ m ih =>
      rw [show Nat.succ m + n = Nat.succ (m+n) by omega]
      simp only [headOffset]
      rw [ih (TM63Uniform.step c)]
      simp [TM63Uniform.run, Int.add_assoc]

theorem headOffset_prep3 (h : Bool) (ls rs : List Bool) :
    headOffset 3 ⟨3, h :: ls, true, false :: rs⟩ = -1 := by
  simp [headOffset, headDelta, TM63Uniform.step,
    TM63Uniform.moveR, TM63Uniform.moveL]

theorem headOffset_d3 (ls rs : List Bool) :
    headOffset 3 ⟨3, ls, true, [true,true,true] ++ rs⟩ = 3 := by
  simp [headOffset, headDelta, TM63Uniform.step,
    TM63Uniform.moveR, TM63Uniform.moveL]

theorem headOffset_d6 (ls rs : List Bool) :
    headOffset 6 ⟨3, [false,true] ++ ls, false,
      [false,true,true,true] ++ rs⟩ = 4 := by
  simp [headOffset, headDelta, TM63Uniform.step,
    TM63Uniform.moveR, TM63Uniform.moveL]

theorem headOffset_d9 (ls rs : List Bool) :
    headOffset 9 ⟨3, [false,false,true] ++ ls, true,
      [false,false,true,true,true] ++ rs⟩ = 3 := by
  simp [headOffset, headDelta, TM63Uniform.step,
    TM63Uniform.moveR, TM63Uniform.moveL]

theorem headOffset_e6 (ls rs : List Bool) :
    headOffset 6 ⟨4, ls, true,
      [true,true,false,false,false] ++ rs⟩ = 4 := by
  simp [headOffset, headDelta, TM63Uniform.step,
    TM63Uniform.moveR, TM63Uniform.moveL]

theorem headOffset_c3 (ls rs : List Bool) :
    headOffset 3 ⟨2, true :: ls, true, rs⟩ = -1 := by
  simp [headOffset, headDelta, TM63Uniform.step,
    TM63Uniform.moveR, TM63Uniform.moveL]

theorem headOffset_ctail0 (b : Bool) (ls rs : List Bool) :
    headOffset 3 ⟨2, [false,true,true,true,true,b] ++ ls, true,
      TM63Uniform.ones 6 ++ rs⟩ = -3 := by
  simp [headOffset, headDelta, TM63Uniform.step,
    TM63Uniform.moveR, TM63Uniform.moveL, TM63Uniform.ones]

theorem headOffset_ctail1 (b : Bool) (ls rs : List Bool) :
    headOffset 3 ⟨3, [true,true,b] ++ ls, true,
      [false,false,false] ++ TM63Uniform.ones 6 ++ rs⟩ = -1 := by
  simp [headOffset, headDelta, TM63Uniform.step,
    TM63Uniform.moveR, TM63Uniform.moveL, TM63Uniform.ones]

theorem headOffset_ctail2 (b : Bool) (ls rs : List Bool) :
    headOffset 3 ⟨3, [true,b] ++ ls, true,
      [false,true,false,false] ++ TM63Uniform.ones 6 ++ rs⟩ = -1 := by
  simp [headOffset, headDelta, TM63Uniform.step,
    TM63Uniform.moveR, TM63Uniform.moveL, TM63Uniform.ones]

theorem headOffset_ctail3 (b : Bool) (ls rs : List Bool) :
    headOffset 3 ⟨3, [b] ++ ls, true,
      [false,true,true,false,false] ++ TM63Uniform.ones 6 ++ rs⟩ = -1 := by
  simp [headOffset, headDelta, TM63Uniform.step,
    TM63Uniform.moveR, TM63Uniform.moveL, TM63Uniform.ones]

end BB6Coverage.Agent48UniformHeadOffset
