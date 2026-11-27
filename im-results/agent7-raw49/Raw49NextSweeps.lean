import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw49NextSweeps
open BB6Coverage BB6Coverage.Agent31Pump

theorem commute_rep (d X Y : List Bool) (h : d ++ X = Y ++ d) (n : Nat) :
    d ++ rep X n = rep Y n ++ d := by
  induction n with
  | zero => simp [rep]
  | succ n ih =>
    simp only [rep]
    rw [← List.append_assoc, h, List.append_assoc, ih, List.append_assoc]
namespace M110140
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨2, [false,true] ++ rep [true,true,false,true,true,false,true,true,false] n ++ [true], []⟩
theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem h0 (n : Nat) : run0 table 10 ⟨2, [false,true] ++ rep [true,true,false,true,true,false,true,true,false] n ++ [true], []⟩ = some ⟨0, rep [true,true,false,true,true,false,true,true,false] n ++ [true], [true,false,false]⟩ := by rfl
theorem one1 (L R : List Bool) : run0 table 9 ⟨0, [] ++ [true,true,false,true,true,false,true,true,false] ++ L, [] ++ R⟩ = some ⟨0, [] ++ L, [] ++ [true,false,false,true,false,false,true,false,false] ++ R⟩ := by rfl
theorem h1 (n : Nat) : run0 table (9*n) ⟨0, rep [true,true,false,true,true,false,true,true,false] n ++ [true], [true,false,false]⟩ = some ⟨0, [true], rep [true,false,false,true,false,false,true,false,false] n ++ [true,false,false]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 0 [] [] [true,true,false,true,true,false,true,true,false] [true,false,false,true,false,false,true,false,false] 9 one1 n ([true]) ([true,false,false]))
theorem h2 (n : Nat) : run0 table 2 ⟨0, [true], rep [true,false,false,true,false,false,true,false,false] n ++ [true,false,false]⟩ = some ⟨0, [false,true], rep [true,false,false,true,false,false,true,false,false] n ++ [true,false,false]⟩ := by rfl
theorem one3 (L R : List Bool) : run0 table 9 ⟨0, [false] ++ L, [] ++ [true,false,false,true,false,false,true,false,false] ++ R⟩ = some ⟨0, [false] ++ [true,false,true,true,false,true,true,false,true] ++ L, [] ++ R⟩ := by rfl
theorem h3 (n : Nat) : run0 table (9*n) ⟨0, [false,true], rep [true,false,false,true,false,false,true,false,false] n ++ [true,false,false]⟩ = some ⟨0, [false] ++ rep [true,false,true,true,false,true,true,false,true] n ++ [true], [true,false,false]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 0 [false] [] [true,false,false,true,false,false,true,false,false] [true,false,true,true,false,true,true,false,true] 9 one3 n ([true]) ([true,false,false]))
theorem h4 (n : Nat) : run0 table 19 ⟨0, [false] ++ rep [true,false,true,true,false,true,true,false,true] n ++ [true], [true,false,false]⟩ = some ⟨4, rep [true,false,true,true,false,true,true,false,true] n ++ [true], [false,true,false,false,true,false,false]⟩ := by rfl
theorem one5 (L R : List Bool) : run0 table 9 ⟨4, [] ++ [true,false,true,true,false,true,true,false,true] ++ L, [] ++ R⟩ = some ⟨4, [] ++ L, [] ++ [false,true,false,false,true,false,false,true,false] ++ R⟩ := by rfl
theorem h5 (n : Nat) : run0 table (9*n) ⟨4, rep [true,false,true,true,false,true,true,false,true] n ++ [true], [false,true,false,false,true,false,false]⟩ = some ⟨4, [true], rep [false,true,false,false,true,false,false,true,false] n ++ [false,true,false,false,true,false,false]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 4 [] [] [true,false,true,true,false,true,true,false,true] [false,true,false,false,true,false,false,true,false] 9 one5 n ([true]) ([false,true,false,false,true,false,false]))
theorem h6 (n : Nat) : run0 table 4 ⟨4, [true], rep [false,true,false,false,true,false,false,true,false] n ++ [false,true,false,false,true,false,false]⟩ = some ⟨4, [false,false,true], rep [false,true,false,false,true,false,false,true,false] n ++ [false,true,false,false,true,false,false]⟩ := by rfl
theorem one7 (L R : List Bool) : run0 table 9 ⟨4, [false] ++ L, [] ++ [false,true,false,false,true,false,false,true,false] ++ R⟩ = some ⟨4, [false] ++ [false,true,true,false,true,true,false,true,true] ++ L, [] ++ R⟩ := by rfl
theorem h7 (n : Nat) : run0 table (9*n) ⟨4, [false,false,true], rep [false,true,false,false,true,false,false,true,false] n ++ [false,true,false,false,true,false,false]⟩ = some ⟨4, [false] ++ rep [false,true,true,false,true,true,false,true,true] n ++ [false,true], [false,true,false,false,true,false,false]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 4 [false] [] [false,true,false,false,true,false,false,true,false] [false,true,true,false,true,true,false,true,true] 9 one7 n ([false,true]) ([false,true,false,false,true,false,false]))
theorem h8 (n : Nat) : run0 table 9 ⟨4, [false] ++ rep [false,true,true,false,true,true,false,true,true] n ++ [false,true], [false,true,false,false,true,false,false]⟩ = some ⟨2, [false,true,true,true,false,true,true,false,true,true] ++ rep [false,true,true,false,true,true,false,true,true] n ++ [false,true], []⟩ := by rfl
theorem endEq (n : Nat) : (⟨2, [false,true,true,true,false,true,true,false,true,true] ++ rep [false,true,true,false,true,true,false,true,true] n ++ [false,true], []⟩ : Z0) = family (n+1) := by
  change (⟨2, [false,true,true,true,false,true,true,false,true,true] ++ rep [false,true,true,false,true,true,false,true,true] n ++ [false,true], []⟩ : Z0) = (⟨2, [false,true,true,true,false,true,true,false,true,true,false] ++ rep [true,true,false,true,true,false,true,true,false] n ++ [true], []⟩ : Z0)
  have hl : [false,true,true,true,false,true,true,false,true,true] ++ rep [false,true,true,false,true,true,false,true,true] n ++ [false,true] = [false,true,true,true,false,true,true,false,true,true,false] ++ rep [true,true,false,true,true,false,true,true,false] n ++ [true] := by
    symm
    calc
      _ = [false,true,true,true,false,true,true,false,true,true] ++ ([false] ++ rep [true,true,false,true,true,false,true,true,false] n) ++ [true] := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
      _ = [false,true,true,true,false,true,true,false,true,true] ++ (rep [false,true,true,false,true,true,false,true,true] n ++ [false]) ++ [true] := by rw [commute_rep [false] [true,true,false,true,true,false,true,true,false] [false,true,true,false,true,true,false,true,true] (by decide)]
      _ = _ := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
  rw [hl]
theorem growth (n : Nat) : run0 table (36*n+44) (family n) = some (family (n+1)) := by
  have h := h0 n
  have h := join0 h (h1 n)
  have h := join0 h (h2 n)
  have h := join0 h (h3 n)
  have h := join0 h (h4 n)
  have h := join0 h (h5 n)
  have h := join0 h (h6 n)
  have h := join0 h (h7 n)
  have h := join0 h (h8 n)
  rw [endEq] at h
  change run0 table _ (family n) = _ at h
  rw [show 36*n+44 = 10 + 9*n + 2 + 9*n + 19 + 9*n + 4 + 9*n + 9 by omega]
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 36*n+44) entry (by intro n; omega) growth m hm
#print axioms never
end M110140

namespace M110141
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨2, [false,true] ++ rep [true,true,false,true,true,false,true,true,false] n ++ [true], []⟩
theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem h0 (n : Nat) : run0 table 10 ⟨2, [false,true] ++ rep [true,true,false,true,true,false,true,true,false] n ++ [true], []⟩ = some ⟨0, rep [true,true,false,true,true,false,true,true,false] n ++ [true], [false,true,false]⟩ := by rfl
theorem one1 (L R : List Bool) : run0 table 9 ⟨0, [] ++ [true,true,false,true,true,false,true,true,false] ++ L, [] ++ R⟩ = some ⟨0, [] ++ L, [] ++ [false,true,false,false,true,false,false,true,false] ++ R⟩ := by rfl
theorem h1 (n : Nat) : run0 table (9*n) ⟨0, rep [true,true,false,true,true,false,true,true,false] n ++ [true], [false,true,false]⟩ = some ⟨0, [true], rep [false,true,false,false,true,false,false,true,false] n ++ [false,true,false]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 0 [] [] [true,true,false,true,true,false,true,true,false] [false,true,false,false,true,false,false,true,false] 9 one1 n ([true]) ([false,true,false]))
theorem h2 (n : Nat) : run0 table 2 ⟨0, [true], rep [false,true,false,false,true,false,false,true,false] n ++ [false,true,false]⟩ = some ⟨0, [false,true], rep [false,true,false,false,true,false,false,true,false] n ++ [false,true,false]⟩ := by rfl
theorem one3 (L R : List Bool) : run0 table 15 ⟨0, [false] ++ L, [] ++ [false,true,false,false,true,false,false,true,false] ++ R⟩ = some ⟨0, [false] ++ [true,false,true,true,false,true,true,false,true] ++ L, [] ++ R⟩ := by rfl
theorem h3 (n : Nat) : run0 table (15*n) ⟨0, [false,true], rep [false,true,false,false,true,false,false,true,false] n ++ [false,true,false]⟩ = some ⟨0, [false] ++ rep [true,false,true,true,false,true,true,false,true] n ++ [true], [false,true,false]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 0 [false] [] [false,true,false,false,true,false,false,true,false] [true,false,true,true,false,true,true,false,true] 15 one3 n ([true]) ([false,true,false]))
theorem h4 (n : Nat) : run0 table 21 ⟨0, [false] ++ rep [true,false,true,true,false,true,true,false,true] n ++ [true], [false,true,false]⟩ = some ⟨4, rep [true,false,true,true,false,true,true,false,true] n ++ [true], [false,false,true,false,false,true,false]⟩ := by rfl
theorem one5 (L R : List Bool) : run0 table 9 ⟨4, [] ++ [true,false,true,true,false,true,true,false,true] ++ L, [] ++ R⟩ = some ⟨4, [] ++ L, [] ++ [false,false,true,false,false,true,false,false,true] ++ R⟩ := by rfl
theorem h5 (n : Nat) : run0 table (9*n) ⟨4, rep [true,false,true,true,false,true,true,false,true] n ++ [true], [false,false,true,false,false,true,false]⟩ = some ⟨4, [true], rep [false,false,true,false,false,true,false,false,true] n ++ [false,false,true,false,false,true,false]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 4 [] [] [true,false,true,true,false,true,true,false,true] [false,false,true,false,false,true,false,false,true] 9 one5 n ([true]) ([false,false,true,false,false,true,false]))
theorem h6 (n : Nat) : run0 table 6 ⟨4, [true], rep [false,false,true,false,false,true,false,false,true] n ++ [false,false,true,false,false,true,false]⟩ = some ⟨4, [false,false,true], rep [false,false,true,false,false,true,false,false,true] n ++ [false,false,true,false,false,true,false]⟩ := by rfl
theorem one7 (L R : List Bool) : run0 table 15 ⟨4, [false] ++ L, [] ++ [false,false,true,false,false,true,false,false,true] ++ R⟩ = some ⟨4, [false] ++ [false,true,true,false,true,true,false,true,true] ++ L, [] ++ R⟩ := by rfl
theorem h7 (n : Nat) : run0 table (15*n) ⟨4, [false,false,true], rep [false,false,true,false,false,true,false,false,true] n ++ [false,false,true,false,false,true,false]⟩ = some ⟨4, [false] ++ rep [false,true,true,false,true,true,false,true,true] n ++ [false,true], [false,false,true,false,false,true,false]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 4 [false] [] [false,false,true,false,false,true,false,false,true] [false,true,true,false,true,true,false,true,true] 15 one7 n ([false,true]) ([false,false,true,false,false,true,false]))
theorem h8 (n : Nat) : run0 table 13 ⟨4, [false] ++ rep [false,true,true,false,true,true,false,true,true] n ++ [false,true], [false,false,true,false,false,true,false]⟩ = some ⟨2, [false,true,true,true,false,true,true,false,true,true] ++ rep [false,true,true,false,true,true,false,true,true] n ++ [false,true], []⟩ := by rfl
theorem endEq (n : Nat) : (⟨2, [false,true,true,true,false,true,true,false,true,true] ++ rep [false,true,true,false,true,true,false,true,true] n ++ [false,true], []⟩ : Z0) = family (n+1) := by
  change (⟨2, [false,true,true,true,false,true,true,false,true,true] ++ rep [false,true,true,false,true,true,false,true,true] n ++ [false,true], []⟩ : Z0) = (⟨2, [false,true,true,true,false,true,true,false,true,true,false] ++ rep [true,true,false,true,true,false,true,true,false] n ++ [true], []⟩ : Z0)
  have hl : [false,true,true,true,false,true,true,false,true,true] ++ rep [false,true,true,false,true,true,false,true,true] n ++ [false,true] = [false,true,true,true,false,true,true,false,true,true,false] ++ rep [true,true,false,true,true,false,true,true,false] n ++ [true] := by
    symm
    calc
      _ = [false,true,true,true,false,true,true,false,true,true] ++ ([false] ++ rep [true,true,false,true,true,false,true,true,false] n) ++ [true] := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
      _ = [false,true,true,true,false,true,true,false,true,true] ++ (rep [false,true,true,false,true,true,false,true,true] n ++ [false]) ++ [true] := by rw [commute_rep [false] [true,true,false,true,true,false,true,true,false] [false,true,true,false,true,true,false,true,true] (by decide)]
      _ = _ := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
  rw [hl]
theorem growth (n : Nat) : run0 table (48*n+52) (family n) = some (family (n+1)) := by
  have h := h0 n
  have h := join0 h (h1 n)
  have h := join0 h (h2 n)
  have h := join0 h (h3 n)
  have h := join0 h (h4 n)
  have h := join0 h (h5 n)
  have h := join0 h (h6 n)
  have h := join0 h (h7 n)
  have h := join0 h (h8 n)
  rw [endEq] at h
  change run0 table _ (family n) = _ at h
  rw [show 48*n+52 = 10 + 9*n + 2 + 15*n + 21 + 9*n + 6 + 15*n + 13 by omega]
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 48*n+52) entry (by intro n; omega) growth m hm
#print axioms never
end M110141

namespace M130007
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨2, [false,true] ++ rep [false,true,false,true,false,true,false,true] n ++ [true], []⟩
theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem h0 (n : Nat) : run0 table 6 ⟨2, [false,true] ++ rep [false,true,false,true,false,true,false,true] n ++ [true], []⟩ = some ⟨4, rep [false,true,false,true,false,true,false,true] n ++ [true], [true,false,true]⟩ := by rfl
theorem one1 (L R : List Bool) : run0 table 12 ⟨4, [] ++ [false,true,false,true,false,true,false,true] ++ L, [] ++ R⟩ = some ⟨4, [] ++ L, [] ++ [true,false,true,false,true,false,true,false] ++ R⟩ := by rfl
theorem h1 (n : Nat) : run0 table (12*n) ⟨4, rep [false,true,false,true,false,true,false,true] n ++ [true], [true,false,true]⟩ = some ⟨4, [true], rep [true,false,true,false,true,false,true,false] n ++ [true,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 4 [] [] [false,true,false,true,false,true,false,true] [true,false,true,false,true,false,true,false] 12 one1 n ([true]) ([true,false,true]))
theorem h2 (n : Nat) : run0 table 2 ⟨4, [true], rep [true,false,true,false,true,false,true,false] n ++ [true,false,true]⟩ = some ⟨2, [false,true], rep [true,false,true,false,true,false,true,false] n ++ [true,false,true]⟩ := by rfl
theorem one3 (L R : List Bool) : run0 table 8 ⟨2, [false] ++ L, [] ++ [true,false,true,false,true,false,true,false] ++ R⟩ = some ⟨2, [false] ++ [true,false,true,false,true,false,true,false] ++ L, [] ++ R⟩ := by rfl
theorem h3 (n : Nat) : run0 table (8*n) ⟨2, [false,true], rep [true,false,true,false,true,false,true,false] n ++ [true,false,true]⟩ = some ⟨2, [false] ++ rep [true,false,true,false,true,false,true,false] n ++ [true], [true,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 2 [false] [] [true,false,true,false,true,false,true,false] [true,false,true,false,true,false,true,false] 8 one3 n ([true]) ([true,false,true]))
theorem h4 (n : Nat) : run0 table 15 ⟨2, [false] ++ rep [true,false,true,false,true,false,true,false] n ++ [true], [true,false,true]⟩ = some ⟨1, rep [true,false,true,false,true,false,true,false] n ++ [true], [false,true,false,true,false,true]⟩ := by rfl
theorem one5 (L R : List Bool) : run0 table 12 ⟨1, [] ++ [true,false,true,false,true,false,true,false] ++ L, [] ++ R⟩ = some ⟨1, [] ++ L, [] ++ [false,true,false,true,false,true,false,true] ++ R⟩ := by rfl
theorem h5 (n : Nat) : run0 table (12*n) ⟨1, rep [true,false,true,false,true,false,true,false] n ++ [true], [false,true,false,true,false,true]⟩ = some ⟨1, [true], rep [false,true,false,true,false,true,false,true] n ++ [false,true,false,true,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 1 [] [] [true,false,true,false,true,false,true,false] [false,true,false,true,false,true,false,true] 12 one5 n ([true]) ([false,true,false,true,false,true]))
theorem h6 (n : Nat) : run0 table 6 ⟨1, [true], rep [false,true,false,true,false,true,false,true] n ++ [false,true,false,true,false,true]⟩ = some ⟨3, [true,false,true,true], rep [false,true,false,true,false,true,false,true] n ++ [false,true,false,true,false,true]⟩ := by rfl
theorem one7 (L R : List Bool) : run0 table 8 ⟨3, [true] ++ L, [] ++ [false,true,false,true,false,true,false,true] ++ R⟩ = some ⟨3, [true] ++ [false,true,false,true,false,true,false,true] ++ L, [] ++ R⟩ := by rfl
theorem h7 (n : Nat) : run0 table (8*n) ⟨3, [true,false,true,true], rep [false,true,false,true,false,true,false,true] n ++ [false,true,false,true,false,true]⟩ = some ⟨3, [true] ++ rep [false,true,false,true,false,true,false,true] n ++ [false,true,true], [false,true,false,true,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 3 [true] [] [false,true,false,true,false,true,false,true] [false,true,false,true,false,true,false,true] 8 one7 n ([false,true,true]) ([false,true,false,true,false,true]))
theorem h8 (n : Nat) : run0 table 7 ⟨3, [true] ++ rep [false,true,false,true,false,true,false,true] n ++ [false,true,true], [false,true,false,true,false,true]⟩ = some ⟨2, [false,true,false,true,false,true,false,true] ++ rep [false,true,false,true,false,true,false,true] n ++ [false,true,true], []⟩ := by rfl
theorem endEq (n : Nat) : (⟨2, [false,true,false,true,false,true,false,true] ++ rep [false,true,false,true,false,true,false,true] n ++ [false,true,true], []⟩ : Z0) = family (n+1) := by
  change (⟨2, [false,true,false,true,false,true,false,true] ++ rep [false,true,false,true,false,true,false,true] n ++ [false,true,true], []⟩ : Z0) = (⟨2, [false,true,false,true,false,true,false,true,false,true] ++ rep [false,true,false,true,false,true,false,true] n ++ [true], []⟩ : Z0)
  have hl : [false,true,false,true,false,true,false,true] ++ rep [false,true,false,true,false,true,false,true] n ++ [false,true,true] = [false,true,false,true,false,true,false,true,false,true] ++ rep [false,true,false,true,false,true,false,true] n ++ [true] := by
    symm
    calc
      _ = [false,true,false,true,false,true,false,true] ++ ([false,true] ++ rep [false,true,false,true,false,true,false,true] n) ++ [true] := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
      _ = [false,true,false,true,false,true,false,true] ++ (rep [false,true,false,true,false,true,false,true] n ++ [false,true]) ++ [true] := by rw [commute_rep [false,true] [false,true,false,true,false,true,false,true] [false,true,false,true,false,true,false,true] (by decide)]
      _ = _ := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
  rw [hl]
theorem growth (n : Nat) : run0 table (40*n+36) (family n) = some (family (n+1)) := by
  have h := h0 n
  have h := join0 h (h1 n)
  have h := join0 h (h2 n)
  have h := join0 h (h3 n)
  have h := join0 h (h4 n)
  have h := join0 h (h5 n)
  have h := join0 h (h6 n)
  have h := join0 h (h7 n)
  have h := join0 h (h8 n)
  rw [endEq] at h
  change run0 table _ (family n) = _ at h
  rw [show 40*n+36 = 6 + 12*n + 2 + 8*n + 15 + 12*n + 6 + 8*n + 7 by omega]
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 40*n+36) entry (by intro n; omega) growth m hm
#print axioms never
end M130007

namespace M131063
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨true,true,4⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨2, [false,true] ++ rep [true,true,true,true,true] n ++ [true], []⟩
theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem h0 (n : Nat) : run0 table 6 ⟨2, [false,true] ++ rep [true,true,true,true,true] n ++ [true], []⟩ = some ⟨4, rep [true,true,true,true,true] n ++ [true], [true,false,true]⟩ := by rfl
theorem one1 (L R : List Bool) : run0 table 45 ⟨4, [] ++ [true,true,true,true,true] ++ L, [true,false] ++ R⟩ = some ⟨4, [] ++ L, [true,false] ++ [true,true,true,true,true] ++ R⟩ := by rfl
theorem h1 (n : Nat) : run0 table (45*n) ⟨4, rep [true,true,true,true,true] n ++ [true], [true,false,true]⟩ = some ⟨4, [true], [true,false] ++ rep [true,true,true,true,true] n ++ [true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 4 [] [true,false] [true,true,true,true,true] [true,true,true,true,true] 45 one1 n ([true]) ([true]))
theorem h2 (n : Nat) : run0 table 12 ⟨4, [true], [true,false] ++ rep [true,true,true,true,true] n ++ [true]⟩ = some ⟨5, [true,true,true,true], rep [true,true,true,true,true] n ++ [true]⟩ := by rfl
theorem one3 (L R : List Bool) : run0 table 11 ⟨5, [true] ++ L, [] ++ [true,true,true,true,true] ++ R⟩ = some ⟨5, [true] ++ [true,true,true,true,true] ++ L, [] ++ R⟩ := by rfl
theorem h3 (n : Nat) : run0 table (11*n) ⟨5, [true,true,true,true], rep [true,true,true,true,true] n ++ [true]⟩ = some ⟨5, [true] ++ rep [true,true,true,true,true] n ++ [true,true,true], [true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 5 [true] [] [true,true,true,true,true] [true,true,true,true,true] 11 one3 n ([true,true,true]) ([true]))
theorem h4 (n : Nat) : run0 table 4 ⟨5, [true] ++ rep [true,true,true,true,true] n ++ [true,true,true], [true]⟩ = some ⟨2, [false,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true], []⟩ := by rfl
theorem endEq (n : Nat) : (⟨2, [false,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true], []⟩ : Z0) = family (n+1) := by
  change (⟨2, [false,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true], []⟩ : Z0) = (⟨2, [false,true,true,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true], []⟩ : Z0)
  have hl : [false,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true] = [false,true,true,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true] := by
    symm
    calc
      _ = [false,true,true,true,true] ++ ([true,true] ++ rep [true,true,true,true,true] n) ++ [true] := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
      _ = [false,true,true,true,true] ++ (rep [true,true,true,true,true] n ++ [true,true]) ++ [true] := by rw [commute_rep [true,true] [true,true,true,true,true] [true,true,true,true,true] (by decide)]
      _ = _ := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
  rw [hl]
theorem growth (n : Nat) : run0 table (56*n+22) (family n) = some (family (n+1)) := by
  have h := h0 n
  have h := join0 h (h1 n)
  have h := join0 h (h2 n)
  have h := join0 h (h3 n)
  have h := join0 h (h4 n)
  rw [endEq] at h
  change run0 table _ (family n) = _ at h
  rw [show 56*n+22 = 6 + 45*n + 12 + 11*n + 4 by omega]
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 56*n+22) entry (by intro n; omega) growth m hm
#print axioms never
end M131063

namespace M131094
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨true,true,4⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨2, [false,true] ++ rep [true,true,true,true,true] n ++ [true], []⟩
theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem h0 (n : Nat) : run0 table 6 ⟨2, [false,true] ++ rep [true,true,true,true,true] n ++ [true], []⟩ = some ⟨4, rep [true,true,true,true,true] n ++ [true], [true,false,true]⟩ := by rfl
theorem one1 (L R : List Bool) : run0 table 35 ⟨4, [] ++ [true,true,true,true,true] ++ L, [true,false] ++ R⟩ = some ⟨4, [] ++ L, [true,false] ++ [true,true,true,true,true] ++ R⟩ := by rfl
theorem h1 (n : Nat) : run0 table (35*n) ⟨4, rep [true,true,true,true,true] n ++ [true], [true,false,true]⟩ = some ⟨4, [true], [true,false] ++ rep [true,true,true,true,true] n ++ [true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 4 [] [true,false] [true,true,true,true,true] [true,true,true,true,true] 35 one1 n ([true]) ([true]))
theorem h2 (n : Nat) : run0 table 10 ⟨4, [true], [true,false] ++ rep [true,true,true,true,true] n ++ [true]⟩ = some ⟨5, [true,true,true,true], rep [true,true,true,true,true] n ++ [true]⟩ := by rfl
theorem one3 (L R : List Bool) : run0 table 9 ⟨5, [true] ++ L, [] ++ [true,true,true,true,true] ++ R⟩ = some ⟨5, [true] ++ [true,true,true,true,true] ++ L, [] ++ R⟩ := by rfl
theorem h3 (n : Nat) : run0 table (9*n) ⟨5, [true,true,true,true], rep [true,true,true,true,true] n ++ [true]⟩ = some ⟨5, [true] ++ rep [true,true,true,true,true] n ++ [true,true,true], [true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 5 [true] [] [true,true,true,true,true] [true,true,true,true,true] 9 one3 n ([true,true,true]) ([true]))
theorem h4 (n : Nat) : run0 table 4 ⟨5, [true] ++ rep [true,true,true,true,true] n ++ [true,true,true], [true]⟩ = some ⟨2, [false,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true], []⟩ := by rfl
theorem endEq (n : Nat) : (⟨2, [false,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true], []⟩ : Z0) = family (n+1) := by
  change (⟨2, [false,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true], []⟩ : Z0) = (⟨2, [false,true,true,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true], []⟩ : Z0)
  have hl : [false,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true] = [false,true,true,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true] := by
    symm
    calc
      _ = [false,true,true,true,true] ++ ([true,true] ++ rep [true,true,true,true,true] n) ++ [true] := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
      _ = [false,true,true,true,true] ++ (rep [true,true,true,true,true] n ++ [true,true]) ++ [true] := by rw [commute_rep [true,true] [true,true,true,true,true] [true,true,true,true,true] (by decide)]
      _ = _ := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
  rw [hl]
theorem growth (n : Nat) : run0 table (44*n+20) (family n) = some (family (n+1)) := by
  have h := h0 n
  have h := join0 h (h1 n)
  have h := join0 h (h2 n)
  have h := join0 h (h3 n)
  have h := join0 h (h4 n)
  rw [endEq] at h
  change run0 table _ (family n) = _ at h
  rw [show 44*n+20 = 6 + 35*n + 10 + 9*n + 4 by omega]
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 44*n+20) entry (by intro n; omega) growth m hm
#print axioms never
end M131094

namespace M90003
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨2, [false,true] ++ rep [true,true,true,true] n ++ [true], []⟩
theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem h0 (n : Nat) : run0 table 6 ⟨2, [false,true] ++ rep [true,true,true,true] n ++ [true], []⟩ = some ⟨0, rep [true,true,true,true] n ++ [true], [false,false,true]⟩ := by rfl
theorem one1 (L R : List Bool) : run0 table 4 ⟨0, [] ++ [true,true,true,true] ++ L, [] ++ R⟩ = some ⟨0, [] ++ L, [] ++ [false,false,false,false] ++ R⟩ := by rfl
theorem h1 (n : Nat) : run0 table (4*n) ⟨0, rep [true,true,true,true] n ++ [true], [false,false,true]⟩ = some ⟨0, [true], rep [false,false,false,false] n ++ [false,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 0 [] [] [true,true,true,true] [false,false,false,false] 4 one1 n ([true]) ([false,false,true]))
theorem h2 (n : Nat) : run0 table 12 ⟨0, [true], rep [false,false,false,false] n ++ [false,false,true]⟩ = some ⟨3, [true,false,true,true], rep [false,false,false,false] n ++ [false,false,true]⟩ := by rfl
theorem one3 (L R : List Bool) : run0 table 20 ⟨3, [true,false] ++ L, [] ++ [false,false,false,false] ++ R⟩ = some ⟨3, [true,false] ++ [true,true,true,true] ++ L, [] ++ R⟩ := by rfl
theorem h3 (n : Nat) : run0 table (20*n) ⟨3, [true,false,true,true], rep [false,false,false,false] n ++ [false,false,true]⟩ = some ⟨3, [true,false] ++ rep [true,true,true,true] n ++ [true,true], [false,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 3 [true,false] [] [false,false,false,false] [true,true,true,true] 20 one3 n ([true,true]) ([false,false,true]))
theorem h4 (n : Nat) : run0 table 15 ⟨3, [true,false] ++ rep [true,true,true,true] n ++ [true,true], [false,false,true]⟩ = some ⟨2, [false,true,true,true,true] ++ rep [true,true,true,true] n ++ [true,true], []⟩ := by rfl
theorem endEq (n : Nat) : (⟨2, [false,true,true,true,true] ++ rep [true,true,true,true] n ++ [true,true], []⟩ : Z0) = family (n+1) := by
  change (⟨2, [false,true,true,true,true] ++ rep [true,true,true,true] n ++ [true,true], []⟩ : Z0) = (⟨2, [false,true,true,true,true,true] ++ rep [true,true,true,true] n ++ [true], []⟩ : Z0)
  have hl : [false,true,true,true,true] ++ rep [true,true,true,true] n ++ [true,true] = [false,true,true,true,true,true] ++ rep [true,true,true,true] n ++ [true] := by
    symm
    calc
      _ = [false,true,true,true,true] ++ ([true] ++ rep [true,true,true,true] n) ++ [true] := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
      _ = [false,true,true,true,true] ++ (rep [true,true,true,true] n ++ [true]) ++ [true] := by rw [commute_rep [true] [true,true,true,true] [true,true,true,true] (by decide)]
      _ = _ := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
  rw [hl]
theorem growth (n : Nat) : run0 table (24*n+33) (family n) = some (family (n+1)) := by
  have h := h0 n
  have h := join0 h (h1 n)
  have h := join0 h (h2 n)
  have h := join0 h (h3 n)
  have h := join0 h (h4 n)
  rw [endEq] at h
  change run0 table _ (family n) = _ at h
  rw [show 24*n+33 = 6 + 4*n + 12 + 20*n + 15 by omega]
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 24*n+33) entry (by intro n; omega) growth m hm
#print axioms never
end M90003

namespace M90012
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨false,true,0⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨2, [false,true] ++ rep [true,true,true,true] n ++ [true], []⟩
theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem h0 (n : Nat) : run0 table 6 ⟨2, [false,true] ++ rep [true,true,true,true] n ++ [true], []⟩ = some ⟨0, rep [true,true,true,true] n ++ [true], [false,false,true]⟩ := by rfl
theorem one1 (L R : List Bool) : run0 table 6 ⟨0, [] ++ [true,true,true,true] ++ L, [] ++ R⟩ = some ⟨0, [] ++ L, [] ++ [false,false,false,false] ++ R⟩ := by rfl
theorem h1 (n : Nat) : run0 table (6*n) ⟨0, rep [true,true,true,true] n ++ [true], [false,false,true]⟩ = some ⟨0, [true], rep [false,false,false,false] n ++ [false,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 0 [] [] [true,true,true,true] [false,false,false,false] 6 one1 n ([true]) ([false,false,true]))
theorem h2 (n : Nat) : run0 table 12 ⟨0, [true], rep [false,false,false,false] n ++ [false,false,true]⟩ = some ⟨3, [true,false,true,true], rep [false,false,false,false] n ++ [false,false,true]⟩ := by rfl
theorem one3 (L R : List Bool) : run0 table 20 ⟨3, [true,false] ++ L, [] ++ [false,false,false,false] ++ R⟩ = some ⟨3, [true,false] ++ [true,true,true,true] ++ L, [] ++ R⟩ := by rfl
theorem h3 (n : Nat) : run0 table (20*n) ⟨3, [true,false,true,true], rep [false,false,false,false] n ++ [false,false,true]⟩ = some ⟨3, [true,false] ++ rep [true,true,true,true] n ++ [true,true], [false,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 3 [true,false] [] [false,false,false,false] [true,true,true,true] 20 one3 n ([true,true]) ([false,false,true]))
theorem h4 (n : Nat) : run0 table 15 ⟨3, [true,false] ++ rep [true,true,true,true] n ++ [true,true], [false,false,true]⟩ = some ⟨2, [false,true,true,true,true] ++ rep [true,true,true,true] n ++ [true,true], []⟩ := by rfl
theorem endEq (n : Nat) : (⟨2, [false,true,true,true,true] ++ rep [true,true,true,true] n ++ [true,true], []⟩ : Z0) = family (n+1) := by
  change (⟨2, [false,true,true,true,true] ++ rep [true,true,true,true] n ++ [true,true], []⟩ : Z0) = (⟨2, [false,true,true,true,true,true] ++ rep [true,true,true,true] n ++ [true], []⟩ : Z0)
  have hl : [false,true,true,true,true] ++ rep [true,true,true,true] n ++ [true,true] = [false,true,true,true,true,true] ++ rep [true,true,true,true] n ++ [true] := by
    symm
    calc
      _ = [false,true,true,true,true] ++ ([true] ++ rep [true,true,true,true] n) ++ [true] := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
      _ = [false,true,true,true,true] ++ (rep [true,true,true,true] n ++ [true]) ++ [true] := by rw [commute_rep [true] [true,true,true,true] [true,true,true,true] (by decide)]
      _ = _ := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
  rw [hl]
theorem growth (n : Nat) : run0 table (26*n+33) (family n) = some (family (n+1)) := by
  have h := h0 n
  have h := join0 h (h1 n)
  have h := join0 h (h2 n)
  have h := join0 h (h3 n)
  have h := join0 h (h4 n)
  rw [endEq] at h
  change run0 table _ (family n) = _ at h
  rw [show 26*n+33 = 6 + 6*n + 12 + 20*n + 15 by omega]
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 26*n+33) entry (by intro n; omega) growth m hm
#print axioms never
end M90012

namespace M90096
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨0, [true], rep [false,false,true,true,false,false,false,true] n ++ [false,false,true]⟩
theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem h0 (n : Nat) : run0 table 4 ⟨0, [true], rep [false,false,true,true,false,false,false,true] n ++ [false,false,true]⟩ = some ⟨3, [true,false,true], rep [false,false,true,true,false,false,false,true] n ++ [false,false,true]⟩ := by rfl
theorem one1 (L R : List Bool) : run0 table 28 ⟨3, [true,false] ++ L, [] ++ [false,false,true,true,false,false,false,true] ++ R⟩ = some ⟨3, [true,false] ++ [true,false,true,true,true,true,true,true] ++ L, [] ++ R⟩ := by rfl
theorem h1 (n : Nat) : run0 table (28*n) ⟨3, [true,false,true], rep [false,false,true,true,false,false,false,true] n ++ [false,false,true]⟩ = some ⟨3, [true,false] ++ rep [true,false,true,true,true,true,true,true] n ++ [true], [false,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 3 [true,false] [] [false,false,true,true,false,false,false,true] [true,false,true,true,true,true,true,true] 28 one1 n ([true]) ([false,false,true]))
theorem h2 (n : Nat) : run0 table 24 ⟨3, [true,false] ++ rep [true,false,true,true,true,true,true,true] n ++ [true], [false,false,true]⟩ = some ⟨1, rep [true,false,true,true,true,true,true,true] n ++ [true], [false,false,true,false,false,true]⟩ := by rfl
theorem one3 (L R : List Bool) : run0 table 16 ⟨1, [] ++ [true,false,true,true,true,true,true,true] ++ L, [false,false] ++ R⟩ = some ⟨1, [] ++ L, [false,false] ++ [true,false,false,false,true,false,false,true] ++ R⟩ := by rfl
theorem h3 (n : Nat) : run0 table (16*n) ⟨1, rep [true,false,true,true,true,true,true,true] n ++ [true], [false,false,true,false,false,true]⟩ = some ⟨1, [true], [false,false] ++ rep [true,false,false,false,true,false,false,true] n ++ [true,false,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 1 [] [false,false] [true,false,true,true,true,true,true,true] [true,false,false,false,true,false,false,true] 16 one3 n ([true]) ([true,false,false,true]))
theorem h4 (n : Nat) : run0 table 28 ⟨1, [true], [false,false] ++ rep [true,false,false,false,true,false,false,true] n ++ [true,false,false,true]⟩ = some ⟨2, [false,true,true,true,true,true], rep [true,false,false,false,true,false,false,true] n ++ [true,false,false,true]⟩ := by rfl
theorem one5 (L R : List Bool) : run0 table 28 ⟨2, [false] ++ L, [] ++ [true,false,false,false,true,false,false,true] ++ R⟩ = some ⟨2, [false] ++ [true,true,true,true,true,false,true,true] ++ L, [] ++ R⟩ := by rfl
theorem h5 (n : Nat) : run0 table (28*n) ⟨2, [false,true,true,true,true,true], rep [true,false,false,false,true,false,false,true] n ++ [true,false,false,true]⟩ = some ⟨2, [false] ++ rep [true,true,true,true,true,false,true,true] n ++ [true,true,true,true,true], [true,false,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 2 [false] [] [true,false,false,false,true,false,false,true] [true,true,true,true,true,false,true,true] 28 one5 n ([true,true,true,true,true]) ([true,false,false,true]))
theorem h6 (n : Nat) : run0 table 25 ⟨2, [false] ++ rep [true,true,true,true,true,false,true,true] n ++ [true,true,true,true,true], [true,false,false,true]⟩ = some ⟨1, rep [true,true,true,true,true,false,true,true] n ++ [true,true,true,true,true], [false,false,true,false,false,true]⟩ := by rfl
theorem one7 (L R : List Bool) : run0 table 16 ⟨1, [] ++ [true,true,true,true,true,false,true,true] ++ L, [] ++ R⟩ = some ⟨1, [] ++ L, [] ++ [false,false,true,false,false,true,true,false] ++ R⟩ := by rfl
theorem h7 (n : Nat) : run0 table (16*n) ⟨1, rep [true,true,true,true,true,false,true,true] n ++ [true,true,true,true,true], [false,false,true,false,false,true]⟩ = some ⟨1, [true,true,true,true,true], rep [false,false,true,false,false,true,true,false] n ++ [false,false,true,false,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 1 [] [] [true,true,true,true,true,false,true,true] [false,false,true,false,false,true,true,false] 16 one7 n ([true,true,true,true,true]) ([false,false,true,false,false,true]))
theorem h8 (n : Nat) : run0 table 13 ⟨1, [true,true,true,true,true], rep [false,false,true,false,false,true,true,false] n ++ [false,false,true,false,false,true]⟩ = some ⟨0, [true], [false,false,true,true,false] ++ rep [false,false,true,false,false,true,true,false] n ++ [false,false,true,false,false,true]⟩ := by rfl
theorem endEq (n : Nat) : (⟨0, [true], [false,false,true,true,false] ++ rep [false,false,true,false,false,true,true,false] n ++ [false,false,true,false,false,true]⟩ : Z0) = family (n+1) := by
  change (⟨0, [true], [false,false,true,true,false] ++ rep [false,false,true,false,false,true,true,false] n ++ [false,false,true,false,false,true]⟩ : Z0) = (⟨0, [true], [false,false,true,true,false,false,false,true] ++ rep [false,false,true,true,false,false,false,true] n ++ [false,false,true]⟩ : Z0)
  have hr : [false,false,true,true,false] ++ rep [false,false,true,false,false,true,true,false] n ++ [false,false,true,false,false,true] = [false,false,true,true,false,false,false,true] ++ rep [false,false,true,true,false,false,false,true] n ++ [false,false,true] := by
    symm
    calc
      _ = [false,false,true,true,false] ++ ([false,false,true] ++ rep [false,false,true,true,false,false,false,true] n) ++ [false,false,true] := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
      _ = [false,false,true,true,false] ++ (rep [false,false,true,false,false,true,true,false] n ++ [false,false,true]) ++ [false,false,true] := by rw [commute_rep [false,false,true] [false,false,true,true,false,false,false,true] [false,false,true,false,false,true,true,false] (by decide)]
      _ = _ := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
  rw [hr]
theorem growth (n : Nat) : run0 table (88*n+94) (family n) = some (family (n+1)) := by
  have h := h0 n
  have h := join0 h (h1 n)
  have h := join0 h (h2 n)
  have h := join0 h (h3 n)
  have h := join0 h (h4 n)
  have h := join0 h (h5 n)
  have h := join0 h (h6 n)
  have h := join0 h (h7 n)
  have h := join0 h (h8 n)
  rw [endEq] at h
  change run0 table _ (family n) = _ at h
  rw [show 88*n+94 = 4 + 28*n + 24 + 16*n + 28 + 28*n + 25 + 16*n + 13 by omega]
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => 88*n+94) entry (by intro n; omega) growth m hm
#print axioms never
end M90096

namespace M90097
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨0, [true], rep [false,false,false,true] n ++ [false,false,true]⟩
theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem h0 (n : Nat) : run0 table 4 ⟨0, [true], rep [false,false,false,true] n ++ [false,false,true]⟩ = some ⟨3, [true,false,true], rep [false,false,false,true] n ++ [false,false,true]⟩ := by rfl
theorem one1 (L R : List Bool) : run0 table 12 ⟨3, [true,false] ++ L, [] ++ [false,false,false,true] ++ R⟩ = some ⟨3, [true,false] ++ [true,false,true,true] ++ L, [] ++ R⟩ := by rfl
theorem h1 (n : Nat) : run0 table (12*n) ⟨3, [true,false,true], rep [false,false,false,true] n ++ [false,false,true]⟩ = some ⟨3, [true,false] ++ rep [true,false,true,true] n ++ [true], [false,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 3 [true,false] [] [false,false,false,true] [true,false,true,true] 12 one1 n ([true]) ([false,false,true]))
theorem h2 (n : Nat) : run0 table 24 ⟨3, [true,false] ++ rep [true,false,true,true] n ++ [true], [false,false,true]⟩ = some ⟨1, rep [true,false,true,true] n ++ [true], [true,false,true,false,false,true]⟩ := by rfl
theorem one3 (L R : List Bool) : run0 table 8 ⟨1, [] ++ [true,false,true,true] ++ L, [true] ++ R⟩ = some ⟨1, [] ++ L, [true] ++ [false,true,false,false] ++ R⟩ := by rfl
theorem h3 (n : Nat) : run0 table (8*n) ⟨1, rep [true,false,true,true] n ++ [true], [true,false,true,false,false,true]⟩ = some ⟨1, [true], [true] ++ rep [false,true,false,false] n ++ [false,true,false,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 1 [] [true] [true,false,true,true] [false,true,false,false] 8 one3 n ([true]) ([false,true,false,false,true]))
theorem h4 (n : Nat) : run0 table 5 ⟨1, [true], [true] ++ rep [false,true,false,false] n ++ [false,true,false,false,true]⟩ = some ⟨0, [true], [false,false] ++ rep [false,true,false,false] n ++ [false,true,false,false,true]⟩ := by rfl
theorem endEq (n : Nat) : (⟨0, [true], [false,false] ++ rep [false,true,false,false] n ++ [false,true,false,false,true]⟩ : Z0) = family (n+1) := by
  change (⟨0, [true], [false,false] ++ rep [false,true,false,false] n ++ [false,true,false,false,true]⟩ : Z0) = (⟨0, [true], [false,false,false,true] ++ rep [false,false,false,true] n ++ [false,false,true]⟩ : Z0)
  have hr : [false,false] ++ rep [false,true,false,false] n ++ [false,true,false,false,true] = [false,false,false,true] ++ rep [false,false,false,true] n ++ [false,false,true] := by
    symm
    calc
      _ = [false,false] ++ ([false,true] ++ rep [false,false,false,true] n) ++ [false,false,true] := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
      _ = [false,false] ++ (rep [false,true,false,false] n ++ [false,true]) ++ [false,false,true] := by rw [commute_rep [false,true] [false,false,false,true] [false,true,false,false] (by decide)]
      _ = _ := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
  rw [hr]
theorem growth (n : Nat) : run0 table (20*n+33) (family n) = some (family (n+1)) := by
  have h := h0 n
  have h := join0 h (h1 n)
  have h := join0 h (h2 n)
  have h := join0 h (h3 n)
  have h := join0 h (h4 n)
  rw [endEq] at h
  change run0 table _ (family n) = _ at h
  rw [show 20*n+33 = 4 + 12*n + 24 + 8*n + 5 by omega]
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => 20*n+33) entry (by intro n; omega) growth m hm
#print axioms never
end M90097

namespace M90098
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,false,3⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨0, [true], rep [false,false,true,true,false,false,false,true] n ++ [false,false,true]⟩
theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem h0 (n : Nat) : run0 table 4 ⟨0, [true], rep [false,false,true,true,false,false,false,true] n ++ [false,false,true]⟩ = some ⟨3, [true,false,true], rep [false,false,true,true,false,false,false,true] n ++ [false,false,true]⟩ := by rfl
theorem one1 (L R : List Bool) : run0 table 28 ⟨3, [true,false] ++ L, [] ++ [false,false,true,true,false,false,false,true] ++ R⟩ = some ⟨3, [true,false] ++ [true,false,true,true,true,true,true,true] ++ L, [] ++ R⟩ := by rfl
theorem h1 (n : Nat) : run0 table (28*n) ⟨3, [true,false,true], rep [false,false,true,true,false,false,false,true] n ++ [false,false,true]⟩ = some ⟨3, [true,false] ++ rep [true,false,true,true,true,true,true,true] n ++ [true], [false,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 3 [true,false] [] [false,false,true,true,false,false,false,true] [true,false,true,true,true,true,true,true] 28 one1 n ([true]) ([false,false,true]))
theorem h2 (n : Nat) : run0 table 24 ⟨3, [true,false] ++ rep [true,false,true,true,true,true,true,true] n ++ [true], [false,false,true]⟩ = some ⟨3, rep [true,false,true,true,true,true,true,true] n ++ [true], [true,false,true,false,false,true]⟩ := by rfl
theorem one3 (L R : List Bool) : run0 table 20 ⟨3, [] ++ [true,false,true,true,true,true,true,true] ++ L, [true,false] ++ R⟩ = some ⟨3, [] ++ L, [true,false] ++ [true,false,false,false,true,false,false,true] ++ R⟩ := by rfl
theorem h3 (n : Nat) : run0 table (20*n) ⟨3, rep [true,false,true,true,true,true,true,true] n ++ [true], [true,false,true,false,false,true]⟩ = some ⟨3, [true], [true,false] ++ rep [true,false,false,false,true,false,false,true] n ++ [true,false,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 3 [] [true,false] [true,false,true,true,true,true,true,true] [true,false,false,false,true,false,false,true] 20 one3 n ([true]) ([true,false,false,true]))
theorem h4 (n : Nat) : run0 table 30 ⟨3, [true], [true,false] ++ rep [true,false,false,false,true,false,false,true] n ++ [true,false,false,true]⟩ = some ⟨2, [false,true,true,true,true,true], rep [true,false,false,false,true,false,false,true] n ++ [true,false,false,true]⟩ := by rfl
theorem one5 (L R : List Bool) : run0 table 28 ⟨2, [false] ++ L, [] ++ [true,false,false,false,true,false,false,true] ++ R⟩ = some ⟨2, [false] ++ [true,true,true,true,true,false,true,true] ++ L, [] ++ R⟩ := by rfl
theorem h5 (n : Nat) : run0 table (28*n) ⟨2, [false,true,true,true,true,true], rep [true,false,false,false,true,false,false,true] n ++ [true,false,false,true]⟩ = some ⟨2, [false] ++ rep [true,true,true,true,true,false,true,true] n ++ [true,true,true,true,true], [true,false,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 2 [false] [] [true,false,false,false,true,false,false,true] [true,true,true,true,true,false,true,true] 28 one5 n ([true,true,true,true,true]) ([true,false,false,true]))
theorem h6 (n : Nat) : run0 table 25 ⟨2, [false] ++ rep [true,true,true,true,true,false,true,true] n ++ [true,true,true,true,true], [true,false,false,true]⟩ = some ⟨3, rep [true,true,true,true,true,false,true,true] n ++ [true,true,true,true,true], [true,false,true,false,false,true]⟩ := by rfl
theorem one7 (L R : List Bool) : run0 table 20 ⟨3, [] ++ [true,true,true,true,true,false,true,true] ++ L, [true] ++ R⟩ = some ⟨3, [] ++ L, [true] ++ [false,true,false,false,true,true,false,false] ++ R⟩ := by rfl
theorem h7 (n : Nat) : run0 table (20*n) ⟨3, rep [true,true,true,true,true,false,true,true] n ++ [true,true,true,true,true], [true,false,true,false,false,true]⟩ = some ⟨3, [true,true,true,true,true], [true] ++ rep [false,true,false,false,true,true,false,false] n ++ [false,true,false,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 3 [] [true] [true,true,true,true,true,false,true,true] [false,true,false,false,true,true,false,false] 20 one7 n ([true,true,true,true,true]) ([false,true,false,false,true]))
theorem h8 (n : Nat) : run0 table 17 ⟨3, [true,true,true,true,true], [true] ++ rep [false,true,false,false,true,true,false,false] n ++ [false,true,false,false,true]⟩ = some ⟨0, [true], [false,false,true,true,false,false] ++ rep [false,true,false,false,true,true,false,false] n ++ [false,true,false,false,true]⟩ := by rfl
theorem endEq (n : Nat) : (⟨0, [true], [false,false,true,true,false,false] ++ rep [false,true,false,false,true,true,false,false] n ++ [false,true,false,false,true]⟩ : Z0) = family (n+1) := by
  change (⟨0, [true], [false,false,true,true,false,false] ++ rep [false,true,false,false,true,true,false,false] n ++ [false,true,false,false,true]⟩ : Z0) = (⟨0, [true], [false,false,true,true,false,false,false,true] ++ rep [false,false,true,true,false,false,false,true] n ++ [false,false,true]⟩ : Z0)
  have hr : [false,false,true,true,false,false] ++ rep [false,true,false,false,true,true,false,false] n ++ [false,true,false,false,true] = [false,false,true,true,false,false,false,true] ++ rep [false,false,true,true,false,false,false,true] n ++ [false,false,true] := by
    symm
    calc
      _ = [false,false,true,true,false,false] ++ ([false,true] ++ rep [false,false,true,true,false,false,false,true] n) ++ [false,false,true] := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
      _ = [false,false,true,true,false,false] ++ (rep [false,true,false,false,true,true,false,false] n ++ [false,true]) ++ [false,false,true] := by rw [commute_rep [false,true] [false,false,true,true,false,false,false,true] [false,true,false,false,true,true,false,false] (by decide)]
      _ = _ := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
  rw [hr]
theorem growth (n : Nat) : run0 table (96*n+100) (family n) = some (family (n+1)) := by
  have h := h0 n
  have h := join0 h (h1 n)
  have h := join0 h (h2 n)
  have h := join0 h (h3 n)
  have h := join0 h (h4 n)
  have h := join0 h (h5 n)
  have h := join0 h (h6 n)
  have h := join0 h (h7 n)
  have h := join0 h (h8 n)
  rw [endEq] at h
  change run0 table _ (family n) = _ at h
  rw [show 96*n+100 = 4 + 28*n + 24 + 20*n + 30 + 28*n + 25 + 20*n + 17 by omega]
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 8 (fun n => 96*n+100) entry (by intro n; omega) growth m hm
#print axioms never
end M90098

namespace M90181
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨2, [false,true] ++ rep [true,true,true,true,false,true,true,true] n ++ [true], []⟩
theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem h0 (n : Nat) : run0 table 6 ⟨2, [false,true] ++ rep [true,true,true,true,false,true,true,true] n ++ [true], []⟩ = some ⟨0, rep [true,true,true,true,false,true,true,true] n ++ [true], [false,false,true]⟩ := by rfl
theorem one1 (L R : List Bool) : run0 table 16 ⟨0, [] ++ [true,true,true,true,false,true,true,true] ++ L, [] ++ R⟩ = some ⟨0, [] ++ L, [] ++ [false,false,false,true,false,false,true,true] ++ R⟩ := by rfl
theorem h1 (n : Nat) : run0 table (16*n) ⟨0, rep [true,true,true,true,false,true,true,true] n ++ [true], [false,false,true]⟩ = some ⟨0, [true], rep [false,false,false,true,false,false,true,true] n ++ [false,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 0 [] [] [true,true,true,true,false,true,true,true] [false,false,false,true,false,false,true,true] 16 one1 n ([true]) ([false,false,true]))
theorem h2 (n : Nat) : run0 table 8 ⟨0, [true], rep [false,false,false,true,false,false,true,true] n ++ [false,false,true]⟩ = some ⟨3, [true,false,true,true], rep [false,false,false,true,false,false,true,true] n ++ [false,false,true]⟩ := by rfl
theorem one3 (L R : List Bool) : run0 table 28 ⟨3, [true,false] ++ L, [] ++ [false,false,false,true,false,false,true,true] ++ R⟩ = some ⟨3, [true,false] ++ [true,true,true,true,true,false,true,true] ++ L, [] ++ R⟩ := by rfl
theorem h3 (n : Nat) : run0 table (28*n) ⟨3, [true,false,true,true], rep [false,false,false,true,false,false,true,true] n ++ [false,false,true]⟩ = some ⟨3, [true,false] ++ rep [true,true,true,true,true,false,true,true] n ++ [true,true], [false,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 3 [true,false] [] [false,false,false,true,false,false,true,true] [true,true,true,true,true,false,true,true] 28 one3 n ([true,true]) ([false,false,true]))
theorem h4 (n : Nat) : run0 table 24 ⟨3, [true,false] ++ rep [true,true,true,true,true,false,true,true] n ++ [true,true], [false,false,true]⟩ = some ⟨1, rep [true,true,true,true,true,false,true,true] n ++ [true,true], [false,false,true,false,false,true]⟩ := by rfl
theorem one5 (L R : List Bool) : run0 table 16 ⟨1, [] ++ [true,true,true,true,true,false,true,true] ++ L, [] ++ R⟩ = some ⟨1, [] ++ L, [] ++ [false,false,true,false,false,true,true,false] ++ R⟩ := by rfl
theorem h5 (n : Nat) : run0 table (16*n) ⟨1, rep [true,true,true,true,true,false,true,true] n ++ [true,true], [false,false,true,false,false,true]⟩ = some ⟨1, [true,true], rep [false,false,true,false,false,true,true,false] n ++ [false,false,true,false,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 1 [] [] [true,true,true,true,true,false,true,true] [false,false,true,false,false,true,true,false] 16 one5 n ([true,true]) ([false,false,true,false,false,true]))
theorem h6 (n : Nat) : run0 table 10 ⟨1, [true,true], rep [false,false,true,false,false,true,true,false] n ++ [false,false,true,false,false,true]⟩ = some ⟨2, [false,true,false,true,true], rep [false,false,true,false,false,true,true,false] n ++ [false,false,true,false,false,true]⟩ := by rfl
theorem one7 (L R : List Bool) : run0 table 28 ⟨2, [false,true,false] ++ L, [] ++ [false,false,true,false,false,true,true,false] ++ R⟩ = some ⟨2, [false,true,false] ++ [true,true,true,true,true,false,true,true] ++ L, [] ++ R⟩ := by rfl
theorem h7 (n : Nat) : run0 table (28*n) ⟨2, [false,true,false,true,true], rep [false,false,true,false,false,true,true,false] n ++ [false,false,true,false,false,true]⟩ = some ⟨2, [false,true,false] ++ rep [true,true,true,true,true,false,true,true] n ++ [true,true], [false,false,true,false,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 2 [false,true,false] [] [false,false,true,false,false,true,true,false] [true,true,true,true,true,false,true,true] 28 one7 n ([true,true]) ([false,false,true,false,false,true]))
theorem h8 (n : Nat) : run0 table 26 ⟨2, [false,true,false] ++ rep [true,true,true,true,true,false,true,true] n ++ [true,true], [false,false,true,false,false,true]⟩ = some ⟨2, [false,true,true,true,true,true,false,true,true] ++ rep [true,true,true,true,true,false,true,true] n ++ [true,true], []⟩ := by rfl
theorem endEq (n : Nat) : (⟨2, [false,true,true,true,true,true,false,true,true] ++ rep [true,true,true,true,true,false,true,true] n ++ [true,true], []⟩ : Z0) = family (n+1) := by
  change (⟨2, [false,true,true,true,true,true,false,true,true] ++ rep [true,true,true,true,true,false,true,true] n ++ [true,true], []⟩ : Z0) = (⟨2, [false,true,true,true,true,true,false,true,true,true] ++ rep [true,true,true,true,false,true,true,true] n ++ [true], []⟩ : Z0)
  have hl : [false,true,true,true,true,true,false,true,true] ++ rep [true,true,true,true,true,false,true,true] n ++ [true,true] = [false,true,true,true,true,true,false,true,true,true] ++ rep [true,true,true,true,false,true,true,true] n ++ [true] := by
    symm
    calc
      _ = [false,true,true,true,true,true,false,true,true] ++ ([true] ++ rep [true,true,true,true,false,true,true,true] n) ++ [true] := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
      _ = [false,true,true,true,true,true,false,true,true] ++ (rep [true,true,true,true,true,false,true,true] n ++ [true]) ++ [true] := by rw [commute_rep [true] [true,true,true,true,false,true,true,true] [true,true,true,true,true,false,true,true] (by decide)]
      _ = _ := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
  rw [hl]
theorem growth (n : Nat) : run0 table (88*n+74) (family n) = some (family (n+1)) := by
  have h := h0 n
  have h := join0 h (h1 n)
  have h := join0 h (h2 n)
  have h := join0 h (h3 n)
  have h := join0 h (h4 n)
  have h := join0 h (h5 n)
  have h := join0 h (h6 n)
  have h := join0 h (h7 n)
  have h := join0 h (h8 n)
  rw [endEq] at h
  change run0 table _ (family n) = _ at h
  rw [show 88*n+74 = 6 + 16*n + 8 + 28*n + 24 + 16*n + 10 + 28*n + 26 by omega]
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 88*n+74) entry (by intro n; omega) growth m hm
#print axioms never
end M90181

namespace M90184
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨true,false,3⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨2, [false] ++ rep [true,true,true,true,true,false,true,true] n ++ [true,true], []⟩
theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem h0 (n : Nat) : run0 table 3 ⟨2, [false] ++ rep [true,true,true,true,true,false,true,true] n ++ [true,true], []⟩ = some ⟨3, rep [true,true,true,true,true,false,true,true] n ++ [true,true], [true,true]⟩ := by rfl
theorem one1 (L R : List Bool) : run0 table 20 ⟨3, [] ++ [true,true,true,true,true,false,true,true] ++ L, [true] ++ R⟩ = some ⟨3, [] ++ L, [true] ++ [false,true,false,false,true,true,false,false] ++ R⟩ := by rfl
theorem h1 (n : Nat) : run0 table (20*n) ⟨3, rep [true,true,true,true,true,false,true,true] n ++ [true,true], [true,true]⟩ = some ⟨3, [true,true], [true] ++ rep [false,true,false,false,true,true,false,false] n ++ [true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 3 [] [true] [true,true,true,true,true,false,true,true] [false,true,false,false,true,true,false,false] 20 one1 n ([true,true]) ([true]))
theorem h2 (n : Nat) : run0 table 20 ⟨3, [true,true], [true] ++ rep [false,true,false,false,true,true,false,false] n ++ [true]⟩ = some ⟨2, [false,true,true,true,true], [true] ++ rep [false,true,false,false,true,true,false,false] n ++ [true]⟩ := by rfl
theorem one3 (L R : List Bool) : run0 table 28 ⟨2, [false] ++ L, [true] ++ [false,true,false,false,true,true,false,false] ++ R⟩ = some ⟨2, [false] ++ [true,true,true,true,true,true,true,false] ++ L, [true] ++ R⟩ := by rfl
theorem h3 (n : Nat) : run0 table (28*n) ⟨2, [false,true,true,true,true], [true] ++ rep [false,true,false,false,true,true,false,false] n ++ [true]⟩ = some ⟨2, [false] ++ rep [true,true,true,true,true,true,true,false] n ++ [true,true,true,true], [true,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 2 [false] [true] [false,true,false,false,true,true,false,false] [true,true,true,true,true,true,true,false] 28 one3 n ([true,true,true,true]) ([true]))
theorem h4 (n : Nat) : run0 table 13 ⟨2, [false] ++ rep [true,true,true,true,true,true,true,false] n ++ [true,true,true,true], [true,true]⟩ = some ⟨4, rep [true,true,true,true,true,true,true,false] n ++ [true,true,true,true], [true,false,false,true]⟩ := by rfl
theorem one5 (L R : List Bool) : run0 table 20 ⟨4, [] ++ [true,true,true,true,true,true,true,false] ++ L, [] ++ R⟩ = some ⟨4, [] ++ L, [] ++ [true,false,false,true,true,false,false,false] ++ R⟩ := by rfl
theorem h5 (n : Nat) : run0 table (20*n) ⟨4, rep [true,true,true,true,true,true,true,false] n ++ [true,true,true,true], [true,false,false,true]⟩ = some ⟨4, [true,true,true,true], rep [true,false,false,true,true,false,false,false] n ++ [true,false,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 4 [] [] [true,true,true,true,true,true,true,false] [true,false,false,true,true,false,false,false] 20 one5 n ([true,true,true,true]) ([true,false,false,true]))
theorem h6 (n : Nat) : run0 table 24 ⟨4, [true,true,true,true], rep [true,false,false,true,true,false,false,false] n ++ [true,false,false,true]⟩ = some ⟨2, [false,true,false,true,true,true,true], rep [true,false,false,true,true,false,false,false] n ++ [true,false,false,true]⟩ := by rfl
theorem one7 (L R : List Bool) : run0 table 28 ⟨2, [false] ++ L, [] ++ [true,false,false,true,true,false,false,false] ++ R⟩ = some ⟨2, [false] ++ [true,false,true,true,true,true,true,true] ++ L, [] ++ R⟩ := by rfl
theorem h7 (n : Nat) : run0 table (28*n) ⟨2, [false,true,false,true,true,true,true], rep [true,false,false,true,true,false,false,false] n ++ [true,false,false,true]⟩ = some ⟨2, [false] ++ rep [true,false,true,true,true,true,true,true] n ++ [true,false,true,true,true,true], [true,false,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 2 [false] [] [true,false,false,true,true,false,false,false] [true,false,true,true,true,true,true,true] 28 one7 n ([true,false,true,true,true,true]) ([true,false,false,true]))
theorem h8 (n : Nat) : run0 table 16 ⟨2, [false] ++ rep [true,false,true,true,true,true,true,true] n ++ [true,false,true,true,true,true], [true,false,false,true]⟩ = some ⟨2, [false,true,true,true,true] ++ rep [true,false,true,true,true,true,true,true] n ++ [true,false,true,true,true,true], []⟩ := by rfl
theorem endEq (n : Nat) : (⟨2, [false,true,true,true,true] ++ rep [true,false,true,true,true,true,true,true] n ++ [true,false,true,true,true,true], []⟩ : Z0) = family (n+1) := by
  change (⟨2, [false,true,true,true,true] ++ rep [true,false,true,true,true,true,true,true] n ++ [true,false,true,true,true,true], []⟩ : Z0) = (⟨2, [false,true,true,true,true,true,false,true,true] ++ rep [true,true,true,true,true,false,true,true] n ++ [true,true], []⟩ : Z0)
  have hl : [false,true,true,true,true] ++ rep [true,false,true,true,true,true,true,true] n ++ [true,false,true,true,true,true] = [false,true,true,true,true,true,false,true,true] ++ rep [true,true,true,true,true,false,true,true] n ++ [true,true] := by
    symm
    calc
      _ = [false,true,true,true,true] ++ ([true,false,true,true] ++ rep [true,true,true,true,true,false,true,true] n) ++ [true,true] := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
      _ = [false,true,true,true,true] ++ (rep [true,false,true,true,true,true,true,true] n ++ [true,false,true,true]) ++ [true,true] := by rw [commute_rep [true,false,true,true] [true,true,true,true,true,false,true,true] [true,false,true,true,true,true,true,true] (by decide)]
      _ = _ := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
  rw [hl]
theorem growth (n : Nat) : run0 table (96*n+76) (family n) = some (family (n+1)) := by
  have h := h0 n
  have h := join0 h (h1 n)
  have h := join0 h (h2 n)
  have h := join0 h (h3 n)
  have h := join0 h (h4 n)
  have h := join0 h (h5 n)
  have h := join0 h (h6 n)
  have h := join0 h (h7 n)
  have h := join0 h (h8 n)
  rw [endEq] at h
  change run0 table _ (family n) = _ at h
  rw [show 96*n+76 = 3 + 20*n + 20 + 28*n + 13 + 20*n + 24 + 28*n + 16 by omega]
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 96*n+76) entry (by intro n; omega) growth m hm
#print axioms never
end M90184

namespace M90197
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨2, [false,true] ++ rep [true,true,true,true] n ++ [true], []⟩
theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem h0 (n : Nat) : run0 table 6 ⟨2, [false,true] ++ rep [true,true,true,true] n ++ [true], []⟩ = some ⟨0, rep [true,true,true,true] n ++ [true], [false,false,true]⟩ := by rfl
theorem one1 (L R : List Bool) : run0 table 4 ⟨0, [] ++ [true,true,true,true] ++ L, [] ++ R⟩ = some ⟨0, [] ++ L, [] ++ [false,false,true,true] ++ R⟩ := by rfl
theorem h1 (n : Nat) : run0 table (4*n) ⟨0, rep [true,true,true,true] n ++ [true], [false,false,true]⟩ = some ⟨0, [true], rep [false,false,true,true] n ++ [false,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 0 [] [] [true,true,true,true] [false,false,true,true] 4 one1 n ([true]) ([false,false,true]))
theorem h2 (n : Nat) : run0 table 8 ⟨0, [true], rep [false,false,true,true] n ++ [false,false,true]⟩ = some ⟨3, [true,false,true,true], rep [false,false,true,true] n ++ [false,false,true]⟩ := by rfl
theorem one3 (L R : List Bool) : run0 table 16 ⟨3, [true,false] ++ L, [] ++ [false,false,true,true] ++ R⟩ = some ⟨3, [true,false] ++ [true,true,true,true] ++ L, [] ++ R⟩ := by rfl
theorem h3 (n : Nat) : run0 table (16*n) ⟨3, [true,false,true,true], rep [false,false,true,true] n ++ [false,false,true]⟩ = some ⟨3, [true,false] ++ rep [true,true,true,true] n ++ [true,true], [false,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 3 [true,false] [] [false,false,true,true] [true,true,true,true] 16 one3 n ([true,true]) ([false,false,true]))
theorem h4 (n : Nat) : run0 table 15 ⟨3, [true,false] ++ rep [true,true,true,true] n ++ [true,true], [false,false,true]⟩ = some ⟨2, [false,true,true,true,true] ++ rep [true,true,true,true] n ++ [true,true], []⟩ := by rfl
theorem endEq (n : Nat) : (⟨2, [false,true,true,true,true] ++ rep [true,true,true,true] n ++ [true,true], []⟩ : Z0) = family (n+1) := by
  change (⟨2, [false,true,true,true,true] ++ rep [true,true,true,true] n ++ [true,true], []⟩ : Z0) = (⟨2, [false,true,true,true,true,true] ++ rep [true,true,true,true] n ++ [true], []⟩ : Z0)
  have hl : [false,true,true,true,true] ++ rep [true,true,true,true] n ++ [true,true] = [false,true,true,true,true,true] ++ rep [true,true,true,true] n ++ [true] := by
    symm
    calc
      _ = [false,true,true,true,true] ++ ([true] ++ rep [true,true,true,true] n) ++ [true] := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
      _ = [false,true,true,true,true] ++ (rep [true,true,true,true] n ++ [true]) ++ [true] := by rw [commute_rep [true] [true,true,true,true] [true,true,true,true] (by decide)]
      _ = _ := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
  rw [hl]
theorem growth (n : Nat) : run0 table (20*n+29) (family n) = some (family (n+1)) := by
  have h := h0 n
  have h := join0 h (h1 n)
  have h := join0 h (h2 n)
  have h := join0 h (h3 n)
  have h := join0 h (h4 n)
  rw [endEq] at h
  change run0 table _ (family n) = _ at h
  rw [show 20*n+29 = 6 + 4*n + 8 + 16*n + 15 by omega]
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 20*n+29) entry (by intro n; omega) growth m hm
#print axioms never
end M90197

namespace M90223
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,4⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨2, [false,true,true] ++ rep [true,true,true,true] n, []⟩
theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem h0 (n : Nat) : run0 table 7 ⟨2, [false,true,true] ++ rep [true,true,true,true] n, []⟩ = some ⟨4, rep [true,true,true,true] n, [true,false,false,true]⟩ := by rfl
theorem one1 (L R : List Bool) : run0 table 68 ⟨4, [] ++ [true,true,true,true] ++ L, [true,false,false] ++ R⟩ = some ⟨4, [] ++ L, [true,false,false] ++ [true,true,true,true] ++ R⟩ := by rfl
theorem h1 (n : Nat) : run0 table (68*n) ⟨4, rep [true,true,true,true] n, [true,false,false,true]⟩ = some ⟨4, [], [true,false,false] ++ rep [true,true,true,true] n ++ [true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 4 [] [true,false,false] [true,true,true,true] [true,true,true,true] 68 one1 n ([]) ([true]))
theorem h2 (n : Nat) : run0 table 19 ⟨4, [], [true,false,false] ++ rep [true,true,true,true] n ++ [true]⟩ = some ⟨3, [true,false,true,true,true,true], rep [true,true,true,true] n ++ [true]⟩ := by rfl
theorem one3 (L R : List Bool) : run0 table 12 ⟨3, [true,false] ++ L, [] ++ [true,true,true,true] ++ R⟩ = some ⟨3, [true,false] ++ [true,true,true,true] ++ L, [] ++ R⟩ := by rfl
theorem h3 (n : Nat) : run0 table (12*n) ⟨3, [true,false,true,true,true,true], rep [true,true,true,true] n ++ [true]⟩ = some ⟨3, [true,false] ++ rep [true,true,true,true] n ++ [true,true,true,true], [true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 3 [true,false] [] [true,true,true,true] [true,true,true,true] 12 one3 n ([true,true,true,true]) ([true]))
theorem h4 (n : Nat) : run0 table 5 ⟨3, [true,false] ++ rep [true,true,true,true] n ++ [true,true,true,true], [true]⟩ = some ⟨2, [false,true,true] ++ rep [true,true,true,true] n ++ [true,true,true,true], []⟩ := by rfl
theorem endEq (n : Nat) : (⟨2, [false,true,true] ++ rep [true,true,true,true] n ++ [true,true,true,true], []⟩ : Z0) = family (n+1) := by
  change (⟨2, [false,true,true] ++ rep [true,true,true,true] n ++ [true,true,true,true], []⟩ : Z0) = (⟨2, [false,true,true,true,true,true,true] ++ rep [true,true,true,true] n, []⟩ : Z0)
  have hl : [false,true,true] ++ rep [true,true,true,true] n ++ [true,true,true,true] = [false,true,true,true,true,true,true] ++ rep [true,true,true,true] n := by
    symm
    calc
      _ = [false,true,true] ++ ([true,true,true,true] ++ rep [true,true,true,true] n) ++ [] := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
      _ = [false,true,true] ++ (rep [true,true,true,true] n ++ [true,true,true,true]) ++ [] := by rw [commute_rep [true,true,true,true] [true,true,true,true] [true,true,true,true] (by decide)]
      _ = _ := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
  rw [hl]
theorem growth (n : Nat) : run0 table (80*n+31) (family n) = some (family (n+1)) := by
  have h := h0 n
  have h := join0 h (h1 n)
  have h := join0 h (h2 n)
  have h := join0 h (h3 n)
  have h := join0 h (h4 n)
  rw [endEq] at h
  change run0 table _ (family n) = _ at h
  rw [show 80*n+31 = 7 + 68*n + 19 + 12*n + 5 by omega]
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 80*n+31) entry (by intro n; omega) growth m hm
#print axioms never
end M90223

namespace M90243
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨2, [false,true] ++ rep [true,true,true,true,false,true,true,true] n ++ [true], []⟩
theorem entry : run0 table 2 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem h0 (n : Nat) : run0 table 6 ⟨2, [false,true] ++ rep [true,true,true,true,false,true,true,true] n ++ [true], []⟩ = some ⟨0, rep [true,true,true,true,false,true,true,true] n ++ [true], [false,false,true]⟩ := by rfl
theorem one1 (L R : List Bool) : run0 table 16 ⟨0, [] ++ [true,true,true,true,false,true,true,true] ++ L, [] ++ R⟩ = some ⟨0, [] ++ L, [] ++ [false,false,false,true,false,false,true,true] ++ R⟩ := by rfl
theorem h1 (n : Nat) : run0 table (16*n) ⟨0, rep [true,true,true,true,false,true,true,true] n ++ [true], [false,false,true]⟩ = some ⟨0, [true], rep [false,false,false,true,false,false,true,true] n ++ [false,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 0 [] [] [true,true,true,true,false,true,true,true] [false,false,false,true,false,false,true,true] 16 one1 n ([true]) ([false,false,true]))
theorem h2 (n : Nat) : run0 table 14 ⟨0, [true], rep [false,false,false,true,false,false,true,true] n ++ [false,false,true]⟩ = some ⟨3, [true,false,true,true], rep [false,false,false,true,false,false,true,true] n ++ [false,false,true]⟩ := by rfl
theorem one3 (L R : List Bool) : run0 table 28 ⟨3, [true,false] ++ L, [] ++ [false,false,false,true,false,false,true,true] ++ R⟩ = some ⟨3, [true,false] ++ [true,true,true,true,true,false,true,true] ++ L, [] ++ R⟩ := by rfl
theorem h3 (n : Nat) : run0 table (28*n) ⟨3, [true,false,true,true], rep [false,false,false,true,false,false,true,true] n ++ [false,false,true]⟩ = some ⟨3, [true,false] ++ rep [true,true,true,true,true,false,true,true] n ++ [true,true], [false,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 3 [true,false] [] [false,false,false,true,false,false,true,true] [true,true,true,true,true,false,true,true] 28 one3 n ([true,true]) ([false,false,true]))
theorem h4 (n : Nat) : run0 table 24 ⟨3, [true,false] ++ rep [true,true,true,true,true,false,true,true] n ++ [true,true], [false,false,true]⟩ = some ⟨1, rep [true,true,true,true,true,false,true,true] n ++ [true,true], [false,false,true,false,false,true]⟩ := by rfl
theorem one5 (L R : List Bool) : run0 table 16 ⟨1, [] ++ [true,true,true,true,true,false,true,true] ++ L, [] ++ R⟩ = some ⟨1, [] ++ L, [] ++ [false,false,true,false,false,true,true,false] ++ R⟩ := by rfl
theorem h5 (n : Nat) : run0 table (16*n) ⟨1, rep [true,true,true,true,true,false,true,true] n ++ [true,true], [false,false,true,false,false,true]⟩ = some ⟨1, [true,true], rep [false,false,true,false,false,true,true,false] n ++ [false,false,true,false,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 1 [] [] [true,true,true,true,true,false,true,true] [false,false,true,false,false,true,true,false] 16 one5 n ([true,true]) ([false,false,true,false,false,true]))
theorem h6 (n : Nat) : run0 table 16 ⟨1, [true,true], rep [false,false,true,false,false,true,true,false] n ++ [false,false,true,false,false,true]⟩ = some ⟨2, [false,true,false,true,true], rep [false,false,true,false,false,true,true,false] n ++ [false,false,true,false,false,true]⟩ := by rfl
theorem one7 (L R : List Bool) : run0 table 28 ⟨2, [false,true,false] ++ L, [] ++ [false,false,true,false,false,true,true,false] ++ R⟩ = some ⟨2, [false,true,false] ++ [true,true,true,true,true,false,true,true] ++ L, [] ++ R⟩ := by rfl
theorem h7 (n : Nat) : run0 table (28*n) ⟨2, [false,true,false,true,true], rep [false,false,true,false,false,true,true,false] n ++ [false,false,true,false,false,true]⟩ = some ⟨2, [false,true,false] ++ rep [true,true,true,true,true,false,true,true] n ++ [true,true], [false,false,true,false,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 2 [false,true,false] [] [false,false,true,false,false,true,true,false] [true,true,true,true,true,false,true,true] 28 one7 n ([true,true]) ([false,false,true,false,false,true]))
theorem h8 (n : Nat) : run0 table 26 ⟨2, [false,true,false] ++ rep [true,true,true,true,true,false,true,true] n ++ [true,true], [false,false,true,false,false,true]⟩ = some ⟨2, [false,true,true,true,true,true,false,true,true] ++ rep [true,true,true,true,true,false,true,true] n ++ [true,true], []⟩ := by rfl
theorem endEq (n : Nat) : (⟨2, [false,true,true,true,true,true,false,true,true] ++ rep [true,true,true,true,true,false,true,true] n ++ [true,true], []⟩ : Z0) = family (n+1) := by
  change (⟨2, [false,true,true,true,true,true,false,true,true] ++ rep [true,true,true,true,true,false,true,true] n ++ [true,true], []⟩ : Z0) = (⟨2, [false,true,true,true,true,true,false,true,true,true] ++ rep [true,true,true,true,false,true,true,true] n ++ [true], []⟩ : Z0)
  have hl : [false,true,true,true,true,true,false,true,true] ++ rep [true,true,true,true,true,false,true,true] n ++ [true,true] = [false,true,true,true,true,true,false,true,true,true] ++ rep [true,true,true,true,false,true,true,true] n ++ [true] := by
    symm
    calc
      _ = [false,true,true,true,true,true,false,true,true] ++ ([true] ++ rep [true,true,true,true,false,true,true,true] n) ++ [true] := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
      _ = [false,true,true,true,true,true,false,true,true] ++ (rep [true,true,true,true,true,false,true,true] n ++ [true]) ++ [true] := by rw [commute_rep [true] [true,true,true,true,false,true,true,true] [true,true,true,true,true,false,true,true] (by decide)]
      _ = _ := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
  rw [hl]
theorem growth (n : Nat) : run0 table (88*n+86) (family n) = some (family (n+1)) := by
  have h := h0 n
  have h := join0 h (h1 n)
  have h := join0 h (h2 n)
  have h := join0 h (h3 n)
  have h := join0 h (h4 n)
  have h := join0 h (h5 n)
  have h := join0 h (h6 n)
  have h := join0 h (h7 n)
  have h := join0 h (h8 n)
  rw [endEq] at h
  change run0 table _ (family n) = _ at h
  rw [show 88*n+86 = 6 + 16*n + 14 + 28*n + 24 + 16*n + 16 + 28*n + 26 by omega]
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 2 (fun n => 88*n+86) entry (by intro n; omega) growth m hm
#print axioms never
end M90243

namespace M90111
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨0, [], [false,false,true] ++ rep [false,false] n ++ [true,false] ++ rep [false,true] n ++ [false,true]⟩
theorem entry : run0 table 18 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem h0 (n : Nat) : run0 table 3 ⟨0, [], [false,false,true] ++ rep [false,false] n ++ [true,false] ++ rep [false,true] n ++ [false,true]⟩ = some ⟨3, [true,false,true,true], rep [false,false] n ++ [true,false] ++ rep [false,true] n ++ [false,true]⟩ := by rfl
theorem one1 (L R : List Bool) : run0 table 10 ⟨3, [true,false,true,true] ++ L, [] ++ [false,false] ++ R⟩ = some ⟨3, [true,false,true,true] ++ [true,true] ++ L, [] ++ R⟩ := by rfl
theorem h1 (n : Nat) : run0 table (10*n) ⟨3, [true,false,true,true], rep [false,false] n ++ [true,false] ++ rep [false,true] n ++ [false,true]⟩ = some ⟨3, [true,false,true,true] ++ rep [true,true] n, [true,false] ++ rep [false,true] n ++ [false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 3 [true,false,true,true] [] [false,false] [true,true] 10 one1 n ([]) ([true,false] ++ rep [false,true] n ++ [false,true]))
theorem h2 (n : Nat) : run0 table 14 ⟨3, [true,false,true,true] ++ rep [true,true] n, [true,false] ++ rep [false,true] n ++ [false,true]⟩ = some ⟨4, rep [true,true] n, [false,false,true,false,false,true] ++ rep [false,true] n ++ [false,true]⟩ := by rfl
theorem one3 (L R : List Bool) : run0 table 2 ⟨4, [] ++ [true,true] ++ L, [false,false] ++ R⟩ = some ⟨4, [] ++ L, [false,false] ++ [false,false] ++ R⟩ := by rfl
theorem h3 (n : Nat) : run0 table (2*n) ⟨4, rep [true,true] n, [false,false,true,false,false,true] ++ rep [false,true] n ++ [false,true]⟩ = some ⟨4, [], [false,false] ++ rep [false,false] n ++ [true,false,false,true] ++ rep [false,true] n ++ [false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 4 [] [false,false] [true,true] [false,false] 2 one3 n ([]) ([true,false,false,true] ++ rep [false,true] n ++ [false,true]))
theorem h4 (n : Nat) : run0 table 9 ⟨4, [], [false,false] ++ rep [false,false] n ++ [true,false,false,true] ++ rep [false,true] n ++ [false,true]⟩ = some ⟨0, [], [false,false,true,false,false] ++ rep [false,false] n ++ [true,false,false,true] ++ rep [false,true] n ++ [false,true]⟩ := by rfl
theorem endEq (n : Nat) : (⟨0, [], [false,false,true,false,false] ++ rep [false,false] n ++ [true,false,false,true] ++ rep [false,true] n ++ [false,true]⟩ : Z0) = family (n+1) := by
  simp only [family,rep,List.append_assoc,List.cons_append] <;> rfl
theorem growth (n : Nat) : run0 table (12*n+26) (family n) = some (family (n+1)) := by
  have h := h0 n
  have h := join0 h (h1 n)
  have h := join0 h (h2 n)
  have h := join0 h (h3 n)
  have h := join0 h (h4 n)
  rw [endEq] at h
  change run0 table _ (family n) = _ at h
  rw [show 12*n+26 = 3 + 10*n + 14 + 2*n + 9 by omega]
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 18 (fun n => 12*n+26) entry (by intro n; omega) growth m hm
#print axioms never
end M90111

namespace M90217
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨0, [], [false,false,true] ++ rep [false,false] n ++ [true,false] ++ rep [false,true] n ++ [false,true]⟩
theorem entry : run0 table 14 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem h0 (n : Nat) : run0 table 3 ⟨0, [], [false,false,true] ++ rep [false,false] n ++ [true,false] ++ rep [false,true] n ++ [false,true]⟩ = some ⟨3, [true,false,true,true], rep [false,false] n ++ [true,false] ++ rep [false,true] n ++ [false,true]⟩ := by rfl
theorem one1 (L R : List Bool) : run0 table 10 ⟨3, [true,false,true,true] ++ L, [] ++ [false,false] ++ R⟩ = some ⟨3, [true,false,true,true] ++ [true,true] ++ L, [] ++ R⟩ := by rfl
theorem h1 (n : Nat) : run0 table (10*n) ⟨3, [true,false,true,true], rep [false,false] n ++ [true,false] ++ rep [false,true] n ++ [false,true]⟩ = some ⟨3, [true,false,true,true] ++ rep [true,true] n, [true,false] ++ rep [false,true] n ++ [false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 3 [true,false,true,true] [] [false,false] [true,true] 10 one1 n ([]) ([true,false] ++ rep [false,true] n ++ [false,true]))
theorem h2 (n : Nat) : run0 table 14 ⟨3, [true,false,true,true] ++ rep [true,true] n, [true,false] ++ rep [false,true] n ++ [false,true]⟩ = some ⟨4, rep [true,true] n, [false,false,true,false,false,true] ++ rep [false,true] n ++ [false,true]⟩ := by rfl
theorem one3 (L R : List Bool) : run0 table 2 ⟨4, [] ++ [true,true] ++ L, [false,false] ++ R⟩ = some ⟨4, [] ++ L, [false,false] ++ [false,false] ++ R⟩ := by rfl
theorem h3 (n : Nat) : run0 table (2*n) ⟨4, rep [true,true] n, [false,false,true,false,false,true] ++ rep [false,true] n ++ [false,true]⟩ = some ⟨4, [], [false,false] ++ rep [false,false] n ++ [true,false,false,true] ++ rep [false,true] n ++ [false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 4 [] [false,false] [true,true] [false,false] 2 one3 n ([]) ([true,false,false,true] ++ rep [false,true] n ++ [false,true]))
theorem h4 (n : Nat) : run0 table 5 ⟨4, [], [false,false] ++ rep [false,false] n ++ [true,false,false,true] ++ rep [false,true] n ++ [false,true]⟩ = some ⟨0, [], [false,false,true,false,false] ++ rep [false,false] n ++ [true,false,false,true] ++ rep [false,true] n ++ [false,true]⟩ := by rfl
theorem endEq (n : Nat) : (⟨0, [], [false,false,true,false,false] ++ rep [false,false] n ++ [true,false,false,true] ++ rep [false,true] n ++ [false,true]⟩ : Z0) = family (n+1) := by
  simp only [family,rep,List.append_assoc,List.cons_append] <;> rfl
theorem growth (n : Nat) : run0 table (12*n+22) (family n) = some (family (n+1)) := by
  have h := h0 n
  have h := join0 h (h1 n)
  have h := join0 h (h2 n)
  have h := join0 h (h3 n)
  have h := join0 h (h4 n)
  rw [endEq] at h
  change run0 table _ (family n) = _ at h
  rw [show 12*n+22 = 3 + 10*n + 14 + 2*n + 5 by omega]
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 14 (fun n => 12*n+22) entry (by intro n; omega) growth m hm
#print axioms never
end M90217
end BB6.Agent7Raw49NextSweeps
