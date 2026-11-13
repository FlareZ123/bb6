import S1ResetBaseAlignment
import RootShift
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent48ResetBaseEmbedding

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset

/-- Cell formulas at head zero, exposing the nearest-first left/right streams. -/
@[simp] theorem s1Config_left_cell_zero
    (L n m a z b i : Nat) :
    (s1Config L n m a z b (0:Int)).tape (-(i:Int)) =
      sideBit (s1LeftFacing L n m a z) i := by
  simpa using s1Config_left_cell L n m a z b (0:Int) i

@[simp] theorem s1Config_right_cell_zero
    (L n m a z b i : Nat) :
    (s1Config L n m a z b (0:Int)).tape (1+(i:Int)) =
      sideBit (s1PhysicalRight b) i := by
  simpa using s1Config_right_cell L n m a z b (0:Int) i

/-- Cell formulas at the five-cell-shifted output head. -/
@[simp] theorem s1Config_left_cell_five
    (L n m a z b i : Nat) :
    (s1Config L n m a z b (5:Int)).tape (5-(i:Int)) =
      sideBit (s1LeftFacing L n m a z) i := by
  exact s1Config_left_cell L n m a z b (5:Int) i

@[simp] theorem s1Config_right_cell_five
    (L n m a z b i : Nat) :
    (s1Config L n m a z b (5:Int)).tape (6+(i:Int)) =
      sideBit (s1PhysicalRight b) i := by
  simpa using s1Config_right_cell L n m a z b (5:Int) i

/-- The finite input frame agrees cellwise with the S1 source tape on
its entire touched interval. -/
theorem resetBase_input_inside (L m : Nat) (hL : 0 < L) (hm : m < 3)
    (x : Int) (hin : resetBaseInside m x = true) :
    (embed (resetBaseInput m)).tape x =
      (s1Config L 1 m 0 0 0 0).tape x := by
  have hm' : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  rcases hm' with rfl | rfl | rfl
  · have hbound : -7 ≤ x ∧ x ≤ 14 := by
      simpa [resetBaseInside] using hin
    have hcases : x = (-7:Int) ∨ x = (-6:Int) ∨ x = (-5:Int) ∨ x = (-4:Int) ∨ x = (-3:Int) ∨ x = (-2:Int) ∨ x = (-1:Int) ∨ x = (0:Int) ∨ x = (1:Int) ∨ x = (2:Int) ∨ x = (3:Int) ∨ x = (4:Int) ∨ x = (5:Int) ∨ x = (6:Int) ∨ x = (7:Int) ∨ x = (8:Int) ∨ x = (9:Int) ∨ x = (10:Int) ∨ x = (11:Int) ∨ x = (12:Int) ∨ x = (13:Int) ∨ x = (14:Int) := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21
    all_goals subst x
    all_goals simp [embed, resetBaseInput, resetBaseInput0,
      s1Config_left_cell_zero, s1Config_right_cell_zero,
      resetBase_input_leftStream L 0 hL,
      s1PhysicalRight, s0PhysicalRight, s0RightFacing,
      markerWord, d0, d1, d1pow, sideBit]
  · have hbound : -8 ≤ x ∧ x ≤ 14 := by
      simpa [resetBaseInside] using hin
    have hcases : x = (-8:Int) ∨ x = (-7:Int) ∨ x = (-6:Int) ∨ x = (-5:Int) ∨ x = (-4:Int) ∨ x = (-3:Int) ∨ x = (-2:Int) ∨ x = (-1:Int) ∨ x = (0:Int) ∨ x = (1:Int) ∨ x = (2:Int) ∨ x = (3:Int) ∨ x = (4:Int) ∨ x = (5:Int) ∨ x = (6:Int) ∨ x = (7:Int) ∨ x = (8:Int) ∨ x = (9:Int) ∨ x = (10:Int) ∨ x = (11:Int) ∨ x = (12:Int) ∨ x = (13:Int) ∨ x = (14:Int) := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22
    all_goals subst x
    all_goals simp [embed, resetBaseInput, resetBaseInput1,
      s1Config_left_cell_zero, s1Config_right_cell_zero,
      resetBase_input_leftStream L 1 hL,
      s1PhysicalRight, s0PhysicalRight, s0RightFacing,
      markerWord, d0, d1, d1pow, sideBit]
  · have hbound : -8 ≤ x ∧ x ≤ 14 := by
      simpa [resetBaseInside] using hin
    have hcases : x = (-8:Int) ∨ x = (-7:Int) ∨ x = (-6:Int) ∨ x = (-5:Int) ∨ x = (-4:Int) ∨ x = (-3:Int) ∨ x = (-2:Int) ∨ x = (-1:Int) ∨ x = (0:Int) ∨ x = (1:Int) ∨ x = (2:Int) ∨ x = (3:Int) ∨ x = (4:Int) ∨ x = (5:Int) ∨ x = (6:Int) ∨ x = (7:Int) ∨ x = (8:Int) ∨ x = (9:Int) ∨ x = (10:Int) ∨ x = (11:Int) ∨ x = (12:Int) ∨ x = (13:Int) ∨ x = (14:Int) := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22
    all_goals subst x
    all_goals simp [embed, resetBaseInput, resetBaseInput2,
      s1Config_left_cell_zero, s1Config_right_cell_zero,
      resetBase_input_leftStream L 2 hL,
      s1PhysicalRight, s0PhysicalRight, s0RightFacing,
      markerWord, d0, d1, d1pow, sideBit]

/-- The finite output frame agrees cellwise with the proposed successor S1
tape on its entire touched interval. -/
theorem resetBase_output_inside (L m : Nat) (hL : 0 < L) (hm : m < 3)
    (x : Int) (hin : resetBaseInside m x = true) :
    (embed (resetBaseOutput m)).tape x =
      (s1Config L 0 ((m+2)%3) (resetDelta m) 0 0 5).tape x := by
  have hm' : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  rcases hm' with rfl | rfl | rfl
  · have hbound : -7 ≤ x ∧ x ≤ 14 := by
      simpa [resetBaseInside] using hin
    have hcases : x = (-7:Int) ∨ x = (-6:Int) ∨ x = (-5:Int) ∨ x = (-4:Int) ∨ x = (-3:Int) ∨ x = (-2:Int) ∨ x = (-1:Int) ∨ x = (0:Int) ∨ x = (1:Int) ∨ x = (2:Int) ∨ x = (3:Int) ∨ x = (4:Int) ∨ x = (5:Int) ∨ x = (6:Int) ∨ x = (7:Int) ∨ x = (8:Int) ∨ x = (9:Int) ∨ x = (10:Int) ∨ x = (11:Int) ∨ x = (12:Int) ∨ x = (13:Int) ∨ x = (14:Int) := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21
    all_goals subst x
    all_goals simp [embed, resetBaseOutput, resetBaseOutput0,
      s1Config_left_cell_five, s1Config_right_cell_five,
      resetBase_output_leftStream L 0 hL,
      s1PhysicalRight, s0PhysicalRight, s0RightFacing,
      resetDelta, markerWord, d0, d1, d1pow, sideBit]
  · have hbound : -8 ≤ x ∧ x ≤ 14 := by
      simpa [resetBaseInside] using hin
    have hcases : x = (-8:Int) ∨ x = (-7:Int) ∨ x = (-6:Int) ∨ x = (-5:Int) ∨ x = (-4:Int) ∨ x = (-3:Int) ∨ x = (-2:Int) ∨ x = (-1:Int) ∨ x = (0:Int) ∨ x = (1:Int) ∨ x = (2:Int) ∨ x = (3:Int) ∨ x = (4:Int) ∨ x = (5:Int) ∨ x = (6:Int) ∨ x = (7:Int) ∨ x = (8:Int) ∨ x = (9:Int) ∨ x = (10:Int) ∨ x = (11:Int) ∨ x = (12:Int) ∨ x = (13:Int) ∨ x = (14:Int) := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22
    all_goals subst x
    all_goals simp [embed, resetBaseOutput, resetBaseOutput1,
      s1Config_left_cell_five, s1Config_right_cell_five,
      resetBase_output_leftStream L 1 hL,
      s1PhysicalRight, s0PhysicalRight, s0RightFacing,
      resetDelta, markerWord, d0, d1, d1pow, sideBit]
  · have hbound : -8 ≤ x ∧ x ≤ 14 := by
      simpa [resetBaseInside] using hin
    have hcases : x = (-8:Int) ∨ x = (-7:Int) ∨ x = (-6:Int) ∨ x = (-5:Int) ∨ x = (-4:Int) ∨ x = (-3:Int) ∨ x = (-2:Int) ∨ x = (-1:Int) ∨ x = (0:Int) ∨ x = (1:Int) ∨ x = (2:Int) ∨ x = (3:Int) ∨ x = (4:Int) ∨ x = (5:Int) ∨ x = (6:Int) ∨ x = (7:Int) ∨ x = (8:Int) ∨ x = (9:Int) ∨ x = (10:Int) ∨ x = (11:Int) ∨ x = (12:Int) ∨ x = (13:Int) ∨ x = (14:Int) := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22
    all_goals subst x
    all_goals simp [embed, resetBaseOutput, resetBaseOutput2,
      s1Config_left_cell_five, s1Config_right_cell_five,
      resetBase_output_leftStream L 2 hL,
      s1PhysicalRight, s0PhysicalRight, s0RightFacing,
      resetDelta, markerWord, d0, d1, d1pow, sideBit]

/-- Config extensionality without relying on a generated Config.ext theorem. -/
theorem config_ext_by_fields (c d : Config)
    (hs : c.state = d.state) (hh : c.head = d.head)
    (ht : ∀ x, c.tape x = d.tape x) : c = d := by
  cases c with
  | mk cs ch ct =>
    cases d with
    | mk ds dh dt =>
      have hs' : cs = ds := hs
      have hh' : ch = dh := hh
      have ht' : ct = dt := funext ht
      subst ds
      subst dh
      subst dt
      rfl

/-- Lift pointwise inside/outside tape agreements to an exact framed Config
equality. -/
theorem frame_eq_of_cellwise (inside : Int → Bool) (background : Int → Bool)
    (c d : Config) (hs : c.state = d.state) (hh : c.head = d.head)
    (hin : ∀ x, inside x = true → c.tape x = d.tape x)
    (hout : ∀ x, inside x = false → background x = d.tape x) :
    frame inside background c = d := by
  apply config_ext_by_fields c d hs hh
  intro x
  by_cases h : inside x = true
  · simp [frame, h, hin x h]
  · have hfalse : inside x = false := by
      cases hv : inside x <;> simp_all
    simp [frame, hfalse, hout x hfalse]

/-- The input local frame is exactly the S1 source configuration. -/
theorem resetBase_input_frame_eq (L m : Nat) (hL : 0 < L) (hm : m < 3) :
    frame (resetBaseInside m) (s1Config L 1 m 0 0 0 0).tape
      (embed (resetBaseInput m)) =
        s1Config L 1 m 0 0 0 0 := by
  apply frame_eq_of_cellwise
  · simp [embed, resetBaseInput, resetBaseInput0, resetBaseInput1,
      resetBaseInput2, s1Config, s0Config]
  · simp [embed, resetBaseInput, resetBaseInput0, resetBaseInput1,
      resetBaseInput2, s1Config, s0Config]
  · intro x hx
    exact resetBase_input_inside L m hL hm x hx
  · intro x hx
    rfl

/-- The output local frame is exactly the successor S1 configuration;
the infinite exterior is supplied by resetBase_s1_outside. -/
theorem resetBase_output_frame_eq (L m : Nat) (hL : 0 < L) (hm : m < 3) :
    frame (resetBaseInside m) (s1Config L 1 m 0 0 0 0).tape
      (embed (resetBaseOutput m)) =
        s1Config L 0 ((m+2)%3) (resetDelta m) 0 0 5 := by
  apply frame_eq_of_cellwise
  · simp [embed, resetBaseOutput, resetBaseOutput0, resetBaseOutput1,
      resetBaseOutput2, s1Config, s0Config]
  · simp [embed, resetBaseOutput, resetBaseOutput0, resetBaseOutput1,
      resetBaseOutput2, s1Config, s0Config]
  · intro x hx
    exact resetBase_output_inside L m hL hm x hx
  · intro x hx
    exact resetBase_s1_outside L m hL hm x hx

/-- Concrete source reset-prefix theorem for n=1 and a=b=0, at head zero. -/
theorem resetBase_s1_run_zeroHead (L m : Nat) (hL : 0 < L) (hm : m < 3) :
    run tm2 (resetPrefixCost m 1 0 0)
      (s1Config L 1 m 0 0 0 0) =
    some (s1Config L 0 ((m+2)%3) (resetDelta m) 0 0 5) := by
  have hinput := resetBase_input_frame_eq L m hL hm
  have houtput := resetBase_output_frame_eq L m hL hm
  have hbase := resetBase_frame m hm (s1Config L 1 m 0 0 0 0).tape
  rw [hinput, houtput] at hbase
  simpa [resetBase_cost_eq] using hbase

/-- S1 encodings commute with arbitrary head translation. -/
theorem s1Config_shift (L n m a z b : Nat) (h0 h1 : Int) :
    shiftConfig (h1-h0) (s1Config L n m a z b h0) =
      s1Config L n m a z b h1 := by
  apply config_ext_by_fields
  · rfl
  · simp [shiftConfig]
  · intro x
    by_cases hx : x ≤ h1
    · have hle : x-(h1-h0) ≤ h0 := by omega
      have hidx : h0-(x-(h1-h0)) = h1-x := by omega
      simp [shiftConfig, s1Config, s0Config, s0Tape, hx, hle, hidx]
    · have hgt : ¬ x-(h1-h0) ≤ h0 := by omega
      have hidx : x-(h1-h0)-h0-1 = x-h1-1 := by omega
      simp [shiftConfig, s1Config, s0Config, s0Tape, hx, hgt, hidx]

/-- The n=1, a=b=0 reset-prefix source run at every absolute head position. -/
theorem resetBase_s1_run (L m : Nat) (hL : 0 < L) (hm : m < 3) (h : Int) :
    run tm2 (resetPrefixCost m 1 0 0)
      (s1Config L 1 m 0 0 0 h) =
    some (s1Config L 0 ((m+2)%3) (resetDelta m) 0 0 (h+5)) := by
  let c0 := s1Config L 1 m 0 0 0 0
  let c1 := s1Config L 0 ((m+2)%3) (resetDelta m) 0 0 5
  have hshiftIn : shiftConfig h c0 = s1Config L 1 m 0 0 0 h := by
    simpa [c0] using s1Config_shift L 1 m 0 0 0 0 h
  have hshiftOut :
      shiftConfig h c1 =
        s1Config L 0 ((m+2)%3) (resetDelta m) 0 0 (h+5) := by
    have hdelta : (h+5:Int)-5 = h := by omega
    simpa [c1, hdelta] using
      s1Config_shift L 0 ((m+2)%3) (resetDelta m) 0 0 5 (h+5)
  calc
    run tm2 (resetPrefixCost m 1 0 0) (s1Config L 1 m 0 0 0 h) =
        run tm2 (resetPrefixCost m 1 0 0) (shiftConfig h c0) := by
          rw [← hshiftIn]
    _ = (run tm2 (resetPrefixCost m 1 0 0) c0).map (shiftConfig h) :=
      shift_run h tm2 c0 (resetPrefixCost m 1 0 0)
    _ = (some c1).map (shiftConfig h) := by
      rw [resetBase_s1_run_zeroHead L m hL hm]
    _ = some (shiftConfig h c1) := rfl
    _ = some (s1Config L 0 ((m+2)%3) (resetDelta m) 0 0 (h+5)) := by
      rw [hshiftOut]

#print axioms BB6Coverage.Agent48ResetBaseEmbedding.resetBase_s1_run

end BB6Coverage.Agent48ResetBaseEmbedding
