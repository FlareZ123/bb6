import SweepPumping
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39Stack468

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

namespace Md0
theorem phase0 (n : Nat) (X Y : List Bool) : run0 table 8 ⟨0,[false,false,false,false] ++ X,[false,false,false,false,true,false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y⟩ = some ⟨2,[false,false,false,false,true,false,false,false] ++ X,[true,false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨2,[false] ++ L,[true,false,false] ++ [false,true,false,false] ++ R⟩ = some ⟨2,[false,true,true,false,false] ++ L,[true,false,false] ++ R⟩ := by rfl

theorem phase1 (n : Nat) (X Y : List Bool) : run0 table (4*n) ⟨2,[false,false,false,false,true,false,false,false] ++ X,[true,false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y⟩ = some ⟨2,[false] ++ rep [true,true,false,false] n ++ [false,false,false,true,false,false,false] ++ X,[true,false,false,true] ++ Y⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false] [false,true,false,false] [true,true,false,false] 4 local1 n ([false,false,false,true,false,false,false] ++ X) ([true] ++ Y)

theorem phase2 (n : Nat) (X Y : List Bool) : run0 table 8 ⟨2,[false] ++ rep [true,true,false,false] n ++ [false,false,false,true,false,false,false] ++ X,[true,false,false,true] ++ Y⟩ = some ⟨0,[false] ++ rep [true,true,false,false] n ++ [false,false,false,true,false,false,false] ++ X,[false,false,false,true] ++ Y⟩ := by rfl

theorem finalL (n : Nat) (X Y : List Bool) : [false] ++ rep [true,true,false,false] n ++ [false,false,false,true,false,false,false] ++ X = rep [false,true,true,false] n ++ [false,false,false,false,true,false,false,false] ++ X := by
  calc
    _ = rep [false,true,true,false] n ++ [false,false,false,false,true,false,false,false] ++ X := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) ([false,false,false,true,false,false,false] ++ X) [true,true,false] false n

theorem epoch (n : Nat) (X Y : List Bool) : run0 table (16+4*n) ⟨0,[false,false,false,false] ++ X,[false,false,false,false,true,false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y⟩ = some ⟨0,rep [false,true,true,false] n ++ [false,false,false,false,true,false,false,false] ++ X,[false,false,false,true] ++ Y⟩ := by
  have H := (join0 (join0 (phase0 n X Y) (phase1 n X Y)) (phase2 n X Y))
  rw [finalL n X Y] at H
  rw [show 8+4*n+8=16+4*n by omega] at H
  exact H
end Md0

theorem d0_zero (X Y : List Bool) : run0 table 16 ⟨0,[false,false,false,false] ++ X,[false,false,false,true] ++ Y⟩ = some ⟨0,[true,false,false,false] ++ X,[false,false,false,true] ++ Y⟩ := by rfl

namespace Md1
theorem phase0 (n : Nat) (X Y : List Bool) : run0 table 6 ⟨0,[true,false,false,false] ++ X,[false,false,false,false,true,false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y⟩ = some ⟨0,[false,false] ++ X,[false,false,true,false,false,false,true,false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨0,[false] ++ L,[false,false,true,false,false,false,true,false,false] ++ [false,true,false,false] ++ R⟩ = some ⟨0,[false,false,false,true,true] ++ L,[false,false,true,false,false,false,true,false,false] ++ R⟩ := by rfl

theorem phase1 (n : Nat) (X Y : List Bool) : run0 table (4*n) ⟨0,[false,false] ++ X,[false,false,true,false,false,false,true,false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y⟩ = some ⟨0,[false] ++ rep [false,false,true,true] n ++ [false] ++ X,[false,false,true,false,false,false,true,false,false,true] ++ Y⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [false] [false,false,true,false,false,false,true,false,false] [false,true,false,false] [false,false,true,true] 4 local1 n ([false] ++ X) ([true] ++ Y)

theorem phase2 (n : Nat) (X Y : List Bool) : run0 table 14 ⟨0,[false] ++ rep [false,false,true,true] n ++ [false] ++ X,[false,false,true,false,false,false,true,false,false,true] ++ Y⟩ = some ⟨0,[false,true,true,false,false,true,true] ++ rep [false,false,true,true] n ++ [false] ++ X,[false,false,false,true] ++ Y⟩ := by rfl

theorem finalL (n : Nat) (X Y : List Bool) : [false,true,true,false,false,true,true] ++ rep [false,false,true,true] n ++ [false] ++ X = rep [false,true,true,false] n ++ [false,true,true,false,false,true,true,false] ++ X := by
  calc
    _ = [false,true,true,false,false,true] ++ rep [true,false,false,true] n ++ [true,false] ++ X := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([false,true,true,false,false,true]) ([false] ++ X) [false,false,true] true n
    _ = [false,true,true,false,false] ++ rep [true,true,false,false] n ++ [true,true,false] ++ X := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([false,true,true,false,false]) ([true,false] ++ X) [true,false,false] true n
    _ = [false,true,true,false] ++ rep [false,true,true,false] n ++ [false,true,true,false] ++ X := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([false,true,true,false]) ([true,true,false] ++ X) [true,true,false] false n
    _ = [false,true,true] ++ rep [false,false,true,true] n ++ [false,false,true,true,false] ++ X := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([false,true,true]) ([false,true,true,false] ++ X) [false,true,true] false n
    _ = [false,true] ++ rep [true,false,false,true] n ++ [true,false,false,true,true,false] ++ X := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([false,true]) ([false,false,true,true,false] ++ X) [false,false,true] true n
    _ = [false] ++ rep [true,true,false,false] n ++ [true,true,false,false,true,true,false] ++ X := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([false]) ([true,false,false,true,true,false] ++ X) [true,false,false] true n
    _ = rep [false,true,true,false] n ++ [false,true,true,false,false,true,true,false] ++ X := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) ([true,true,false,false,true,true,false] ++ X) [true,true,false] false n

theorem epoch (n : Nat) (X Y : List Bool) : run0 table (20+4*n) ⟨0,[true,false,false,false] ++ X,[false,false,false,false,true,false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y⟩ = some ⟨0,rep [false,true,true,false] n ++ [false,true,true,false,false,true,true,false] ++ X,[false,false,false,true] ++ Y⟩ := by
  have H := (join0 (join0 (phase0 n X Y) (phase1 n X Y)) (phase2 n X Y))
  rw [finalL n X Y] at H
  rw [show 6+4*n+14=20+4*n by omega] at H
  exact H
end Md1

theorem d1_zero (X Y : List Bool) : run0 table 16 ⟨0,[true,false,false,false] ++ X,[false,false,false,true] ++ Y⟩ = some ⟨0,[false,true,true,false] ++ X,[false,false,false,true] ++ Y⟩ := by rfl

namespace Md2
theorem phase0 (n : Nat) (X Y : List Bool) : run0 table 8 ⟨0,[false,true,true,false] ++ X,[false,false,false,false,true,false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y⟩ = some ⟨2,[false,false,false,false,true,true,true,false] ++ X,[true,false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨2,[false] ++ L,[true,false,false] ++ [false,true,false,false] ++ R⟩ = some ⟨2,[false,true,true,false,false] ++ L,[true,false,false] ++ R⟩ := by rfl

theorem phase1 (n : Nat) (X Y : List Bool) : run0 table (4*n) ⟨2,[false,false,false,false,true,true,true,false] ++ X,[true,false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y⟩ = some ⟨2,[false] ++ rep [true,true,false,false] n ++ [false,false,false,true,true,true,false] ++ X,[true,false,false,true] ++ Y⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false] [false,true,false,false] [true,true,false,false] 4 local1 n ([false,false,false,true,true,true,false] ++ X) ([true] ++ Y)

theorem phase2 (n : Nat) (X Y : List Bool) : run0 table 8 ⟨2,[false] ++ rep [true,true,false,false] n ++ [false,false,false,true,true,true,false] ++ X,[true,false,false,true] ++ Y⟩ = some ⟨0,[false] ++ rep [true,true,false,false] n ++ [false,false,false,true,true,true,false] ++ X,[false,false,false,true] ++ Y⟩ := by rfl

theorem finalL (n : Nat) (X Y : List Bool) : [false] ++ rep [true,true,false,false] n ++ [false,false,false,true,true,true,false] ++ X = rep [false,true,true,false] n ++ [false,false,false,false,true,true,true,false] ++ X := by
  calc
    _ = rep [false,true,true,false] n ++ [false,false,false,false,true,true,true,false] ++ X := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) ([false,false,false,true,true,true,false] ++ X) [true,true,false] false n

theorem epoch (n : Nat) (X Y : List Bool) : run0 table (16+4*n) ⟨0,[false,true,true,false] ++ X,[false,false,false,false,true,false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y⟩ = some ⟨0,rep [false,true,true,false] n ++ [false,false,false,false,true,true,true,false] ++ X,[false,false,false,true] ++ Y⟩ := by
  have H := (join0 (join0 (phase0 n X Y) (phase1 n X Y)) (phase2 n X Y))
  rw [finalL n X Y] at H
  rw [show 8+4*n+8=16+4*n by omega] at H
  exact H
end Md2

theorem d2_zero (X Y : List Bool) : run0 table 16 ⟨0,[false,true,true,false] ++ X,[false,false,false,true] ++ Y⟩ = some ⟨0,[true,true,true,false] ++ X,[false,false,false,true] ++ Y⟩ := by rfl

namespace Me0
theorem phase0 (n : Nat) (X Y : List Bool) : run0 table 8 ⟨0,[],[false,false,false,false,true,false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y⟩ = some ⟨2,[false,false,false,false,true],[true,false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨2,[false] ++ L,[true,false,false] ++ [false,true,false,false] ++ R⟩ = some ⟨2,[false,true,true,false,false] ++ L,[true,false,false] ++ R⟩ := by rfl

theorem phase1 (n : Nat) (X Y : List Bool) : run0 table (4*n) ⟨2,[false,false,false,false,true],[true,false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y⟩ = some ⟨2,[false] ++ rep [true,true,false,false] n ++ [false,false,false,true],[true,false,false,true] ++ Y⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false] [false,true,false,false] [true,true,false,false] 4 local1 n ([false,false,false,true]) ([true] ++ Y)

theorem phase2 (n : Nat) (X Y : List Bool) : run0 table 8 ⟨2,[false] ++ rep [true,true,false,false] n ++ [false,false,false,true],[true,false,false,true] ++ Y⟩ = some ⟨0,[false] ++ rep [true,true,false,false] n ++ [false,false,false,true],[false,false,false,true] ++ Y⟩ := by rfl

theorem finalL (n : Nat) (X Y : List Bool) : [false] ++ rep [true,true,false,false] n ++ [false,false,false,true] = rep [false,true,true,false] n ++ [false,false,false,false,true] := by
  calc
    _ = rep [false,true,true,false] n ++ [false,false,false,false,true] := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) ([false,false,false,true]) [true,true,false] false n

theorem epoch (n : Nat) (X Y : List Bool) : run0 table (16+4*n) ⟨0,[],[false,false,false,false,true,false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y⟩ = some ⟨0,rep [false,true,true,false] n ++ [false,false,false,false,true],[false,false,false,true] ++ Y⟩ := by
  have H := (join0 (join0 (phase0 n X Y) (phase1 n X Y)) (phase2 n X Y))
  rw [finalL n X Y] at H
  rw [show 8+4*n+8=16+4*n by omega] at H
  exact H
end Me0

theorem e0_zero (X Y : List Bool) : run0 table 16 ⟨0,[],[false,false,false,true] ++ Y⟩ = some ⟨0,[true],[false,false,false,true] ++ Y⟩ := by rfl

namespace Me1
theorem phase0 (n : Nat) (X Y : List Bool) : run0 table 7 ⟨0,[true],[false,false,false,false,true,false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y⟩ = some ⟨1,[false,true],[false,true,false,false,false,true,false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨1,[false] ++ L,[false,true,false,false,false,true,false,false] ++ [false,true,false,false] ++ R⟩ = some ⟨1,[false,true,false,false,true] ++ L,[false,true,false,false,false,true,false,false] ++ R⟩ := by rfl

theorem phase1 (n : Nat) (X Y : List Bool) : run0 table (4*n) ⟨1,[false,true],[false,true,false,false,false,true,false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y⟩ = some ⟨1,[false] ++ rep [true,false,false,true] n ++ [true],[false,true,false,false,false,true,false,false,true] ++ Y⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 1 [false] [false,true,false,false,false,true,false,false] [false,true,false,false] [true,false,false,true] 4 local1 n ([true]) ([true] ++ Y)

theorem phase2 (n : Nat) (X Y : List Bool) : run0 table 13 ⟨1,[false] ++ rep [true,false,false,true] n ++ [true],[false,true,false,false,false,true,false,false,true] ++ Y⟩ = some ⟨0,[false,true,true,false,false,true] ++ rep [true,false,false,true] n ++ [true],[false,false,false,true] ++ Y⟩ := by rfl

theorem finalL (n : Nat) (X Y : List Bool) : [false,true,true,false,false,true] ++ rep [true,false,false,true] n ++ [true] = rep [false,true,true,false] n ++ [false,true,true,false,false,true,true] := by
  calc
    _ = [false,true,true,false,false] ++ rep [true,true,false,false] n ++ [true,true] := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([false,true,true,false,false]) ([true]) [true,false,false] true n
    _ = [false,true,true,false] ++ rep [false,true,true,false] n ++ [false,true,true] := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([false,true,true,false]) ([true,true]) [true,true,false] false n
    _ = [false,true,true] ++ rep [false,false,true,true] n ++ [false,false,true,true] := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([false,true,true]) ([false,true,true]) [false,true,true] false n
    _ = [false,true] ++ rep [true,false,false,true] n ++ [true,false,false,true,true] := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([false,true]) ([false,false,true,true]) [false,false,true] true n
    _ = [false] ++ rep [true,true,false,false] n ++ [true,true,false,false,true,true] := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([false]) ([true,false,false,true,true]) [true,false,false] true n
    _ = rep [false,true,true,false] n ++ [false,true,true,false,false,true,true] := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) ([true,true,false,false,true,true]) [true,true,false] false n

theorem epoch (n : Nat) (X Y : List Bool) : run0 table (20+4*n) ⟨0,[true],[false,false,false,false,true,false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y⟩ = some ⟨0,rep [false,true,true,false] n ++ [false,true,true,false,false,true,true],[false,false,false,true] ++ Y⟩ := by
  have H := (join0 (join0 (phase0 n X Y) (phase1 n X Y)) (phase2 n X Y))
  rw [finalL n X Y] at H
  rw [show 7+4*n+13=20+4*n by omega] at H
  exact H
end Me1

theorem e1_zero (X Y : List Bool) : run0 table 16 ⟨0,[true],[false,false,false,true] ++ Y⟩ = some ⟨0,[false,true,true],[false,false,false,true] ++ Y⟩ := by rfl

namespace Me01
theorem phase0 (n : Nat) (X Y : List Bool) : run0 table 8 ⟨0,[false,true],[false,false,false,false,true,false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y⟩ = some ⟨2,[false,false,false,false,true,true],[true,false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨2,[false] ++ L,[true,false,false] ++ [false,true,false,false] ++ R⟩ = some ⟨2,[false,true,true,false,false] ++ L,[true,false,false] ++ R⟩ := by rfl

theorem phase1 (n : Nat) (X Y : List Bool) : run0 table (4*n) ⟨2,[false,false,false,false,true,true],[true,false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y⟩ = some ⟨2,[false] ++ rep [true,true,false,false] n ++ [false,false,false,true,true],[true,false,false,true] ++ Y⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false] [false,true,false,false] [true,true,false,false] 4 local1 n ([false,false,false,true,true]) ([true] ++ Y)

theorem phase2 (n : Nat) (X Y : List Bool) : run0 table 8 ⟨2,[false] ++ rep [true,true,false,false] n ++ [false,false,false,true,true],[true,false,false,true] ++ Y⟩ = some ⟨0,[false] ++ rep [true,true,false,false] n ++ [false,false,false,true,true],[false,false,false,true] ++ Y⟩ := by rfl

theorem finalL (n : Nat) (X Y : List Bool) : [false] ++ rep [true,true,false,false] n ++ [false,false,false,true,true] = rep [false,true,true,false] n ++ [false,false,false,false,true,true] := by
  calc
    _ = rep [false,true,true,false] n ++ [false,false,false,false,true,true] := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) ([false,false,false,true,true]) [true,true,false] false n

theorem epoch (n : Nat) (X Y : List Bool) : run0 table (16+4*n) ⟨0,[false,true],[false,false,false,false,true,false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y⟩ = some ⟨0,rep [false,true,true,false] n ++ [false,false,false,false,true,true],[false,false,false,true] ++ Y⟩ := by
  have H := (join0 (join0 (phase0 n X Y) (phase1 n X Y)) (phase2 n X Y))
  rw [finalL n X Y] at H
  rw [show 8+4*n+8=16+4*n by omega] at H
  exact H
end Me01

theorem e01_zero (X Y : List Bool) : run0 table 16 ⟨0,[false,true],[false,false,false,true] ++ Y⟩ = some ⟨0,[true,true],[false,false,false,true] ++ Y⟩ := by rfl

namespace Me011
theorem phase0 (n : Nat) (X Y : List Bool) : run0 table 8 ⟨0,[false,true,true],[false,false,false,false,true,false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y⟩ = some ⟨2,[false,false,false,false,true,true,true],[true,false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 4 ⟨2,[false] ++ L,[true,false,false] ++ [false,true,false,false] ++ R⟩ = some ⟨2,[false,true,true,false,false] ++ L,[true,false,false] ++ R⟩ := by rfl

theorem phase1 (n : Nat) (X Y : List Bool) : run0 table (4*n) ⟨2,[false,false,false,false,true,true,true],[true,false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y⟩ = some ⟨2,[false] ++ rep [true,true,false,false] n ++ [false,false,false,true,true,true],[true,false,false,true] ++ Y⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,false,false] [false,true,false,false] [true,true,false,false] 4 local1 n ([false,false,false,true,true,true]) ([true] ++ Y)

theorem phase2 (n : Nat) (X Y : List Bool) : run0 table 8 ⟨2,[false] ++ rep [true,true,false,false] n ++ [false,false,false,true,true,true],[true,false,false,true] ++ Y⟩ = some ⟨0,[false] ++ rep [true,true,false,false] n ++ [false,false,false,true,true,true],[false,false,false,true] ++ Y⟩ := by rfl

theorem finalL (n : Nat) (X Y : List Bool) : [false] ++ rep [true,true,false,false] n ++ [false,false,false,true,true,true] = rep [false,true,true,false] n ++ [false,false,false,false,true,true,true] := by
  calc
    _ = rep [false,true,true,false] n ++ [false,false,false,false,true,true,true] := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) ([false,false,false,true,true,true]) [true,true,false] false n

theorem epoch (n : Nat) (X Y : List Bool) : run0 table (16+4*n) ⟨0,[false,true,true],[false,false,false,false,true,false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y⟩ = some ⟨0,rep [false,true,true,false] n ++ [false,false,false,false,true,true,true],[false,false,false,true] ++ Y⟩ := by
  have H := (join0 (join0 (phase0 n X Y) (phase1 n X Y)) (phase2 n X Y))
  rw [finalL n X Y] at H
  rw [show 8+4*n+8=16+4*n by omega] at H
  exact H
end Me011

theorem e011_zero (X Y : List Bool) : run0 table 16 ⟨0,[false,true,true],[false,false,false,true] ++ Y⟩ = some ⟨0,[true,true,true],[false,false,false,true] ++ Y⟩ := by rfl

theorem pop (X Y : List Bool) : run0 table 8 ⟨0,[true,true,true,false] ++ X,[false,false,false] ++ Y⟩ = some ⟨0,X,[false,false,false,false,true,false,false] ++ Y⟩ := by rfl
theorem popEnd (X Y : List Bool) : run0 table 8 ⟨0,[true,true,true],[false,false,false] ++ Y⟩ = some ⟨0,[],[false,false,false,false,true,false,false] ++ Y⟩ := by rfl
theorem end11 (X Y : List Bool) : run0 table 7 ⟨0,[true,true],[false] ++ Y⟩ = some ⟨0,[],[false,false,false,true] ++ Y⟩ := by rfl

inductive Stack : List Bool → Prop where
  | d0 (L : List Bool) (h : Stack L) : Stack ([false,false,false,false] ++ L)
  | d1 (L : List Bool) (h : Stack L) : Stack ([true,false,false,false] ++ L)
  | d2 (L : List Bool) (h : Stack L) : Stack ([false,true,true,false] ++ L)
  | d3 (L : List Bool) (h : Stack L) : Stack ([true,true,true,false] ++ L)
  | e0 : Stack []
  | e1 : Stack [true]
  | e01 : Stack [false,true]
  | e11 : Stack [true,true]
  | e011 : Stack [false,true,true]
  | e111 : Stack [true,true,true]

def frame (n : Nat) (Y : List Bool) : List Bool := [false,false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y

theorem stackRep (n : Nat) (L : List Bool) (h : Stack L) : Stack (rep [false,true,true,false] n ++ L) := by
  induction n with
  | zero => exact h
  | succ n ih => exact Stack.d2 _ ih

theorem goodStep (L : List Bool) (n : Nat) (Y : List Bool) (h : Stack L) :
    ∃ k L' n' Y', 0 < k ∧ run0 table k ⟨0,L,frame n Y⟩ = some ⟨0,L',frame n' Y'⟩ ∧ Stack L' := by
  cases h with
  | d0 L h =>
    cases n with
    | zero =>
      refine ⟨16, [true,false,false,false] ++ L, 0, Y, by decide, ?_, Stack.d1 _ (h)⟩
      simpa only [frame,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using d0_zero L Y
    | succ n =>
      refine ⟨16+4*n, rep [false,true,true,false] n ++ ([false,false,false,false,true,false,false,false] ++ L), 0, Y, by omega, ?_, stackRep n _ (Stack.d0 _ (Stack.d1 _ (h)))⟩
      simpa only [frame,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using Md0.epoch n L Y
  | d1 L h =>
    cases n with
    | zero =>
      refine ⟨16, [false,true,true,false] ++ L, 0, Y, by decide, ?_, Stack.d2 _ (h)⟩
      simpa only [frame,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using d1_zero L Y
    | succ n =>
      refine ⟨20+4*n, rep [false,true,true,false] n ++ ([false,true,true,false,false,true,true,false] ++ L), 0, Y, by omega, ?_, stackRep n _ (Stack.d2 _ (Stack.d2 _ (h)))⟩
      simpa only [frame,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using Md1.epoch n L Y
  | d2 L h =>
    cases n with
    | zero =>
      refine ⟨16, [true,true,true,false] ++ L, 0, Y, by decide, ?_, Stack.d3 _ (h)⟩
      simpa only [frame,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using d2_zero L Y
    | succ n =>
      refine ⟨16+4*n, rep [false,true,true,false] n ++ ([false,false,false,false,true,true,true,false] ++ L), 0, Y, by omega, ?_, stackRep n _ (Stack.d0 _ (Stack.d3 _ (h)))⟩
      simpa only [frame,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using Md2.epoch n L Y
  | e0 =>
    cases n with
    | zero =>
      refine ⟨16, [true], 0, Y, by decide, ?_, Stack.e1⟩
      simpa only [frame,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using e0_zero [] Y
    | succ n =>
      refine ⟨16+4*n, rep [false,true,true,false] n ++ ([false,false,false,false,true]), 0, Y, by omega, ?_, stackRep n _ (Stack.d0 _ (Stack.e1))⟩
      simpa only [frame,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using Me0.epoch n [] Y
  | e1 =>
    cases n with
    | zero =>
      refine ⟨16, [false,true,true], 0, Y, by decide, ?_, Stack.e011⟩
      simpa only [frame,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using e1_zero [] Y
    | succ n =>
      refine ⟨20+4*n, rep [false,true,true,false] n ++ ([false,true,true,false,false,true,true]), 0, Y, by omega, ?_, stackRep n _ (Stack.d2 _ (Stack.e011))⟩
      simpa only [frame,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using Me1.epoch n [] Y
  | e01 =>
    cases n with
    | zero =>
      refine ⟨16, [true,true], 0, Y, by decide, ?_, Stack.e11⟩
      simpa only [frame,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using e01_zero [] Y
    | succ n =>
      refine ⟨16+4*n, rep [false,true,true,false] n ++ ([false,false,false,false,true,true]), 0, Y, by omega, ?_, stackRep n _ (Stack.d0 _ (Stack.e11))⟩
      simpa only [frame,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using Me01.epoch n [] Y
  | e011 =>
    cases n with
    | zero =>
      refine ⟨16, [true,true,true], 0, Y, by decide, ?_, Stack.e111⟩
      simpa only [frame,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using e011_zero [] Y
    | succ n =>
      refine ⟨16+4*n, rep [false,true,true,false] n ++ ([false,false,false,false,true,true,true]), 0, Y, by omega, ?_, stackRep n _ (Stack.d0 _ (Stack.e111))⟩
      simpa only [frame,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using Me011.epoch n [] Y
  | d3 L h =>
    refine ⟨8, L, n+1, Y, by decide, ?_, h⟩
    simpa only [frame,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using pop L (rep [false,true,false,false] n ++ [true] ++ Y)
  | e111 =>
    refine ⟨8, [], n+1, Y, by decide, ?_, Stack.e0⟩
    simpa only [frame,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using popEnd [] (rep [false,true,false,false] n ++ [true] ++ Y)
  | e11 =>
    refine ⟨7, [], 0, [false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y, by decide, ?_, Stack.e0⟩
    simpa only [frame,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using end11 [] ([false,false] ++ rep [false,true,false,false] n ++ [true] ++ Y)

theorem entry : run0 table 25 ⟨0,[],[]⟩ = some ⟨0,[],frame 0 [true,true]⟩ := by rfl

theorem arbitrarilyLong (N : Nat) : ∃ k c, N ≤ k ∧ run0 table k ⟨0,[],[]⟩ = some c := by
  have h : ∀ N, ∃ k L n Y, N ≤ k ∧ run0 table k ⟨0,[],[]⟩ = some ⟨0,L,frame n Y⟩ ∧ Stack L := by
    intro N
    induction N with
    | zero => exact ⟨25,[],0,[true,true],by omega,entry,Stack.e0⟩
    | succ N ih =>
      obtain ⟨k,L,n,Y,hk,hr,hs⟩ := ih
      obtain ⟨j,L',n',Y',hj,hjrun,hs'⟩ := goodStep L n Y hs
      exact ⟨k+j,L',n',Y',by omega,join0 hr hjrun,hs'⟩
  obtain ⟨k,L,n,Y,hk,hr,_⟩ := h N
  exact ⟨k,_,hk,hr⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,c,ht,hr⟩ := arbitrarilyLong n
  have hz : (zrun table t start).map project = some c :=
    (run_project table t start).trans hr
  cases h : zrun table t start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound table m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms goodStep
#print axioms arbitrarilyLong
#print axioms never
end BB6.Agent11Raw39Stack468
