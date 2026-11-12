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


/-- The preparatory sweep moves the physical head left once per consumed
leading one, independently of the residual tape. -/
theorem headOffset_prep_all (n : Nat) (h : Bool) (ls rs : List Bool) :
    headOffset (3*(n+1))
      ⟨3, TM63Uniform.ones n ++ (h :: ls), true, false :: rs⟩ = -(n+1) := by
  induction n generalizing h ls rs with
  | zero =>
      simpa [TM63Uniform.ones] using headOffset_prep3 h ls rs
  | succ n ih =>
      have hshape : TM63Uniform.ones (n+1) ++ (h :: ls) =
          true :: (TM63Uniform.ones n ++ (h :: ls)) := by
        simp [TM63Uniform.ones, List.replicate_succ]
      calc
        headOffset (3*((n+1)+1))
            ⟨3, TM63Uniform.ones (n+1) ++ (h :: ls), true, false :: rs⟩
          = headOffset 3
              ⟨3, TM63Uniform.ones (n+1) ++ (h :: ls), true, false :: rs⟩
              + headOffset (3*(n+1))
                (TM63Uniform.run 3
                  ⟨3, TM63Uniform.ones (n+1) ++ (h :: ls), true, false :: rs⟩) := by
                rw [show 3*((n+1)+1) = 3 + 3*(n+1) by omega, headOffset_add]
        _ = -1 + (-(n+1)) := by
              rw [hshape, headOffset_prep3, TM63Uniform.prep3]
              exact ih h ls (true :: rs)
        _ = -(n+2) := by omega

/-- The D-loop sweep moves right by exactly three cells per iteration. -/
theorem headOffset_d_loop (k : Nat) (ls rs : List Bool) :
    headOffset (3*k)
      ⟨3, ls, true, TM63Uniform.ones (3*k) ++ rs⟩ = 3*k := by
  induction k generalizing ls rs with
  | zero => simp [headOffset, TM63Uniform.ones]
  | succ k ih =>
      have hsplit : TM63Uniform.ones (3*(k+1)) =
          TM63Uniform.ones (3*k) ++ [true,true,true] := by
        rw [show 3*(k+1) = 3*k+3 by omega, TM63Uniform.ones_add]
        rfl
      calc
        headOffset (3*(k+1))
            ⟨3, ls, true, TM63Uniform.ones (3*(k+1)) ++ rs⟩
          = headOffset (3*k)
              ⟨3, ls, true, TM63Uniform.ones (3*k) ++ ([true,true,true] ++ rs)⟩
              + headOffset 3
                (TM63Uniform.run (3*k)
                  ⟨3, ls, true, TM63Uniform.ones (3*k) ++ ([true,true,true] ++ rs)⟩) := by
                rw [show 3*(k+1) = 3*k+3 by omega, headOffset_add, hsplit]
                simp [List.append_assoc]
        _ = 3*k + 3 := by
              rw [ih, TM63Uniform.d_loop, headOffset_d3]

/-- The C-loop sweep moves left by exactly one cell per iteration. -/
theorem headOffset_c_loop (n : Nat) (ls rs : List Bool) :
    headOffset (3*n)
      ⟨2, TM63Uniform.ones n ++ ls, true, rs⟩ = -n := by
  induction n generalizing ls rs with
  | zero => simp [headOffset, TM63Uniform.ones]
  | succ n ih =>
      have hsplit : TM63Uniform.ones (n+1) ++ ls =
          TM63Uniform.ones n ++ (true :: ls) := by
        simp [TM63Uniform.ones, List.replicate_succ', List.append_assoc]
      calc
        headOffset (3*(n+1))
            ⟨2, TM63Uniform.ones (n+1) ++ ls, true, rs⟩
          = headOffset (3*n)
              ⟨2, TM63Uniform.ones n ++ (true :: ls), true, rs⟩
              + headOffset 3
                (TM63Uniform.run (3*n)
                  ⟨2, TM63Uniform.ones n ++ (true :: ls), true, rs⟩) := by
                rw [show 3*(n+1) = 3*n+3 by omega, headOffset_add, hsplit]
        _ = -n + -1 := by
              rw [ih, TM63Uniform.c_loop, headOffset_c3]
        _ = -(n+1) := by omega

/-- Each E/1 move advances the physical head by one cell. -/
theorem headOffset_e1 (ls rs : List Bool) :
    headOffset 1 ⟨4, ls, true, true :: rs⟩ = 1 := by
  simp [headOffset, headDelta]

/-- The E/1 scan advances exactly one cell per scanned symbol. -/
theorem headOffset_e_loop (n : Nat) (ls rs : List Bool) :
    headOffset n
      ⟨4, ls, true, TM63Uniform.ones n ++ (true :: rs)⟩ = n := by
  induction n generalizing ls rs with
  | zero => simp [headOffset]
  | succ n ih =>
      have hsplit : TM63Uniform.ones (n+1) ++ (true :: rs) =
          TM63Uniform.ones n ++ (true :: true :: rs) := by
        simp [TM63Uniform.ones, List.replicate_succ', List.append_assoc]
      calc
        headOffset (n+1)
            ⟨4, ls, true, TM63Uniform.ones (n+1) ++ (true :: rs)⟩
          = headOffset n
              ⟨4, ls, true, TM63Uniform.ones n ++ (true :: true :: rs)⟩
              + headOffset 1
                (TM63Uniform.run n
                  ⟨4, ls, true, TM63Uniform.ones n ++ (true :: true :: rs)⟩) := by
                rw [headOffset_add, hsplit]
        _ = n + 1 := by
              rw [ih, TM63Uniform.e_loop, headOffset_e1]

/-- The D-boundary's nine-step closing sweep has displacement +3. -/
theorem headOffset_dBoundary9 (k c : Nat) (ls rs : List Bool) :
    headOffset 9
      ⟨3, TM63Uniform.tri k ++ [false,false,true,true,true,true] ++ ls, true,
        [false,false] ++ TM63Uniform.dTail c rs⟩ = 3 := by
  have hleft :
      TM63Uniform.tri k ++ [false,false,true,true,true,true] ++ ls =
        [false,false,true] ++ TM63Uniform.tri k ++ [true,true,true] ++ ls := by
    simpa [List.append_assoc] using
      congrArg (fun x => x ++ [true,true,true] ++ ls) (TM63Uniform.tri_append k)
  have hones : TM63Uniform.ones (3*(c+1)) =
      [true,true,true] ++ TM63Uniform.ones (3*c) := by
    rw [show 3*(c+1) = 3+3*c by omega, TM63Uniform.ones_add]
    rfl
  have hright :
      [false,false] ++ TM63Uniform.dTail c rs =
        [false,false,true,true,true] ++
          (TM63Uniform.ones (3*c) ++ [false,false,false] ++ rs) := by
    simp [TM63Uniform.dTail, hones, List.append_assoc]
  rw [hleft, hright]
  exact headOffset_d9
    (TM63Uniform.tri k ++ [true,true,true] ++ ls)
    (TM63Uniform.ones (3*c) ++ [false,false,false] ++ rs)

/-- The complete D-front sweep has displacement 3k+7. -/
theorem headOffset_dFront (k c : Nat) (ls rs : List Bool) :
    headOffset (15+3*k) (TM63Uniform.dBoundary k c ls rs) = 3*k+7 := by
  have hones : TM63Uniform.ones (3*(k+1)) =
      [true,true,true] ++ TM63Uniform.ones (3*k) := by
    rw [show 3*(k+1) = 3+3*k by omega, TM63Uniform.ones_add]
    rfl
  have hstart :
      TM63Uniform.dBoundary k c ls rs =
        ⟨3, [false,true] ++ ls, false,
          [false,true,true,true] ++
            (TM63Uniform.ones (3*k) ++ [false,false] ++ TM63Uniform.dTail c rs)⟩ := by
    simp [TM63Uniform.dBoundary, hones, List.append_assoc]
  have h6 : headOffset 6 (TM63Uniform.dBoundary k c ls rs) = 4 := by
    rw [hstart]
    exact headOffset_d6 ls
      (TM63Uniform.ones (3*k) ++ [false,false] ++ TM63Uniform.dTail c rs)
  calc
    headOffset (15+3*k) (TM63Uniform.dBoundary k c ls rs)
      = headOffset 6 (TM63Uniform.dBoundary k c ls rs)
          + headOffset (3*k+9)
            (TM63Uniform.run 6 (TM63Uniform.dBoundary k c ls rs)) := by
          rw [show 15+3*k = 6+(3*k+9) by omega, headOffset_add]
    _ = 4 +
          (headOffset (3*k) (TM63Uniform.run 6 (TM63Uniform.dBoundary k c ls rs))
            + headOffset 9
              (TM63Uniform.run (3*k)
                (TM63Uniform.run 6 (TM63Uniform.dBoundary k c ls rs)))) := by
          rw [h6, headOffset_add]
          simp [Int.add_assoc]
    _ = 4 + (3*k + 3) := by
          rw [TM63Uniform.dBoundary6, headOffset_d_loop,
            TM63Uniform.d_loop, headOffset_dBoundary9]
    _ = 3*k+7 := by omega

/-- The four three-step C-tail blocks move left by a total of six cells. -/
theorem headOffset_ctail12 (b : Bool) (ls rs : List Bool) :
    headOffset 12
      ⟨2, [false,true,true,true,true,b] ++ ls, true,
        TM63Uniform.ones 6 ++ rs⟩ = -6 := by
  calc
    headOffset 12
        ⟨2, [false,true,true,true,true,b] ++ ls, true, TM63Uniform.ones 6 ++ rs⟩
      = headOffset 3
          ⟨2, [false,true,true,true,true,b] ++ ls, true, TM63Uniform.ones 6 ++ rs⟩
          + headOffset 9
            (TM63Uniform.run 3
              ⟨2, [false,true,true,true,true,b] ++ ls, true, TM63Uniform.ones 6 ++ rs⟩) := by
            rw [show 12 = 3+9 by decide, headOffset_add]
    _ = headOffset 3
          ⟨2, [false,true,true,true,true,b] ++ ls, true, TM63Uniform.ones 6 ++ rs⟩
          + (headOffset 3
              (TM63Uniform.run 3
                ⟨2, [false,true,true,true,true,b] ++ ls, true, TM63Uniform.ones 6 ++ rs⟩)
            + headOffset 6
              (TM63Uniform.run 3
                (TM63Uniform.run 3
                  ⟨2, [false,true,true,true,true,b] ++ ls, true, TM63Uniform.ones 6 ++ rs⟩))) := by
            rw [show 9 = 3+6 by decide, headOffset_add]
            simp [Int.add_assoc]
    _ = headOffset 3
          ⟨2, [false,true,true,true,true,b] ++ ls, true, TM63Uniform.ones 6 ++ rs⟩
          + (headOffset 3
              (TM63Uniform.run 3
                ⟨2, [false,true,true,true,true,b] ++ ls, true, TM63Uniform.ones 6 ++ rs⟩)
            + (headOffset 3
                (TM63Uniform.run 3
                  (TM63Uniform.run 3
                    ⟨2, [false,true,true,true,true,b] ++ ls, true, TM63Uniform.ones 6 ++ rs⟩))
              + headOffset 3
                (TM63Uniform.run 3
                  (TM63Uniform.run 3
                    (TM63Uniform.run 3
                      ⟨2, [false,true,true,true,true,b] ++ ls, true, TM63Uniform.ones 6 ++ rs⟩))))) := by
            rw [show 6 = 3+3 by decide, headOffset_add]
            simp [Int.add_assoc]
    _ = -3 + (-1 + (-1 + -1)) := by
          rw [headOffset_ctail0, TM63Uniform.ctail0,
            headOffset_ctail1, TM63Uniform.ctail1,
            headOffset_ctail2, TM63Uniform.ctail2,
            headOffset_ctail3]
    _ = -6 := by omega

/-- The fixed 27-step closing block has displacement -11. -/
theorem headOffset_c27 (b : Bool) (ls rs : List Bool) :
    headOffset 27
      ⟨2, [true,true,true,true,true,false,true,true,true,true,b] ++ ls,
        true, true :: rs⟩ = -11 := by
  have hrun :
      TM63Uniform.run 15
        ⟨2, [true,true,true,true,true,false,true,true,true,true,b] ++ ls,
          true, true :: rs⟩ =
        ⟨2, [false,true,true,true,true,b] ++ ls, true,
          TM63Uniform.ones 6 ++ rs⟩ := by
    simpa [TM63Uniform.ones] using
      (TM63Uniform.c_loop 5 ([false,true,true,true,true,b] ++ ls) (true :: rs))
  calc
    headOffset 27
        ⟨2, [true,true,true,true,true,false,true,true,true,true,b] ++ ls,
          true, true :: rs⟩
      = headOffset 15
          ⟨2, [true,true,true,true,true,false,true,true,true,true,b] ++ ls,
            true, true :: rs⟩
          + headOffset 12
            (TM63Uniform.run 15
              ⟨2, [true,true,true,true,true,false,true,true,true,true,b] ++ ls,
                true, true :: rs⟩) := by
            rw [show 27 = 15+12 by decide, headOffset_add]
    _ = -5 + -6 := by
          rw [headOffset_c_loop, hrun, headOffset_ctail12]
    _ = -11 := by omega

/-- The C-loop bridge stage moves left by exactly 3c cells. -/
theorem headOffset_eStageC (c : Nat) (b : Bool) (ls rs : List Bool) :
    headOffset (9*c)
      ⟨2, [true,true,true,true] ++ TM63Uniform.ones (3*c) ++
          [true,false,true,true,true,true,b] ++ ls, true, true :: rs⟩ = -(3*c) := by
  have hin :
      [true,true,true,true] ++ TM63Uniform.ones (3*c) ++
          [true,false,true,true,true,true,b] ++ ls =
        TM63Uniform.ones (3*c) ++ [true,true,true,true] ++
          [true,false,true,true,true,true,b] ++ ls := by
    have four : TM63Uniform.ones 4 = [true,true,true,true] := rfl
    simpa only [four, List.append_assoc] using
      congrArg (fun x => x ++ [true,false,true,true,true,true,b] ++ ls)
        (TM63Uniform.ones_comm 4 (3*c))
  rw [hin]
  have h := headOffset_c_loop (3*c)
    ([true,true,true,true] ++ [true,false,true,true,true,true,b] ++ ls)
    (true :: rs)
  have htime : 9*c = 3*(3*c) := by omega
  rw [htime]
  exact h

/-- The complete E-back sweep has the constant displacement -7. -/
theorem headOffset_eBack (c : Nat) (b : Bool) (ls rs : List Bool) :
    headOffset (33+12*c) (TM63Uniform.eInput c b ls rs) = -7 := by
  have hfirst : headOffset (3*c) (TM63Uniform.eInput c b ls rs) = 3*c := by
    simpa [TM63Uniform.eInput, List.append_assoc] using
      headOffset_e_loop (3*c)
        ([true,false,true,true,true,true,b] ++ ls)
        ([true,false,false,false] ++ rs)
  calc
    headOffset (33+12*c) (TM63Uniform.eInput c b ls rs)
      = headOffset (3*c) (TM63Uniform.eInput c b ls rs)
          + headOffset (6+(9*c+27))
            (TM63Uniform.run (3*c) (TM63Uniform.eInput c b ls rs)) := by
          rw [show 33+12*c = 3*c+(6+(9*c+27)) by omega, headOffset_add]
    _ = 3*c +
          (headOffset 6
              (TM63Uniform.run (3*c) (TM63Uniform.eInput c b ls rs))
            + headOffset (9*c+27)
              (TM63Uniform.run 6
                (TM63Uniform.run (3*c) (TM63Uniform.eInput c b ls rs)))) := by
          rw [hfirst, TM63Uniform.eStage, headOffset_add]
          simp [Int.add_assoc]
    _ = 3*c +
          (4 +
            (headOffset (9*c)
                (TM63Uniform.run 6
                  (TM63Uniform.run (3*c) (TM63Uniform.eInput c b ls rs)))
              + headOffset 27
                (TM63Uniform.run (9*c)
                  (TM63Uniform.run 6
                    (TM63Uniform.run (3*c) (TM63Uniform.eInput c b ls rs)))))) := by
          rw [TM63Uniform.eStage6, headOffset_e6, headOffset_add]
          simp [Int.add_assoc]
    _ = 3*c + (4 + (-3*c + -11)) := by
          rw [headOffset_eStageC, TM63Uniform.eStageC, headOffset_c27]
    _ = -7 := by omega

/-- The zero-D boundary has zero total head displacement. -/
theorem headOffset_dBoundaryZero (c : Nat) (ls rs : List Bool) :
    headOffset (48+12*c) (TM63Uniform.dBoundary 0 c ls rs) = 0 := by
  calc
    headOffset (48+12*c) (TM63Uniform.dBoundary 0 c ls rs)
      = headOffset 15 (TM63Uniform.dBoundary 0 c ls rs)
          + headOffset (33+12*c)
            (TM63Uniform.run 15 (TM63Uniform.dBoundary 0 c ls rs)) := by
          rw [show 48+12*c = 15+(33+12*c) by omega, headOffset_add]
    _ = 7 + -7 := by
          rw [headOffset_dFront, TM63Uniform.dFront]
          simpa [TM63Uniform.tri, TM63Uniform.eInput, List.append_assoc] using
            headOffset_eBack c true ([true,true,true] ++ ls) rs
    _ = 0 := by omega

/-- Every positive D-boundary has net displacement 3(k+1). -/
theorem headOffset_dBoundarySucc (k c : Nat) (ls rs : List Bool) :
    headOffset (48+3*(k+1)+12*c) (TM63Uniform.dBoundary (k+1) c ls rs) =
      3*(k+1) := by
  calc
    headOffset (48+3*(k+1)+12*c) (TM63Uniform.dBoundary (k+1) c ls rs)
      = headOffset (15+3*(k+1)) (TM63Uniform.dBoundary (k+1) c ls rs)
          + headOffset (33+12*c)
            (TM63Uniform.run (15+3*(k+1)) (TM63Uniform.dBoundary (k+1) c ls rs)) := by
          rw [show 48+3*(k+1)+12*c =
            (15+3*(k+1))+(33+12*c) by omega, headOffset_add]
    _ = (3*(k+1)+7) + -7 := by
          rw [headOffset_dFront, TM63Uniform.dFront]
          simpa [TM63Uniform.tri, TM63Uniform.eInput, List.append_assoc] using
            headOffset_eBack c false
              ([false,true] ++ TM63Uniform.tri k ++ [true,true,true] ++ ls) rs
    _ = 3*(k+1) := by omega

/-- The complete counted block has zero net head displacement for every
valuation k and every counter c. -/
theorem headOffset_counted_all (k c : Nat) (ls rs : List Bool) :
    headOffset (48+12*k+12*c) (TM63Uniform.rawStart k c ls rs) = 0 := by
  cases k with
  | zero =>
      simpa [TM63Uniform.rawStart] using headOffset_dBoundaryZero c ls rs
  | succ k =>
      have htime : 3*((3*k+2)+1) = 9*(k+1) := by omega
      have hprep0 := headOffset_prep_all (3*k+2) false
        ([false,true] ++ ls)
        ([true,true,true] ++ [false,false] ++ TM63Uniform.dTail c rs)
      have hprep : headOffset (9*(k+1))
          (TM63Uniform.rawStart (k+1) c ls rs) = -(3*k+3) := by
        rw [← htime] at hprep0
        simpa [TM63Uniform.rawStart, TM63Uniform.ones, List.append_assoc] using hprep0
      calc
        headOffset (48+12*(k+1)+12*c) (TM63Uniform.rawStart (k+1) c ls rs)
          = headOffset (9*(k+1)) (TM63Uniform.rawStart (k+1) c ls rs)
              + headOffset (48+3*(k+1)+12*c)
                (TM63Uniform.run (9*(k+1)) (TM63Uniform.rawStart (k+1) c ls rs)) := by
              rw [show 48+12*(k+1)+12*c =
                9*(k+1)+(48+3*(k+1)+12*c) by omega, headOffset_add]
        _ = -(3*k+3) + 3*(k+1) := by
              rw [hprep, TM63Uniform.rawStart_prep, headOffset_dBoundarySucc]
        _ = 0 := by omega

#print axioms headOffset_counted_all

end BB6Coverage.Agent48UniformHeadOffset
