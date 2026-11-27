import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw49AutoSweeps
open BB6Coverage BB6Coverage.Agent31Pump

theorem commute_rep (d X Y : List Bool) (h : d ++ X = Y ++ d) (n : Nat) :
    d ++ rep X n = rep Y n ++ d := by
  induction n with
  | zero => simp [rep]
  | succ n ih =>
    simp only [rep]
    rw [← List.append_assoc, h, List.append_assoc, ih, List.append_assoc]

namespace M112
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨4, [], [false,false] ++ rep [false,false,true,true] n ++ [false,false,true]⟩
theorem entry : run0 table 12 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem h0 (n : Nat) : run0 table 1 ⟨4, [], [false,false] ++ rep [false,false,true,true] n ++ [false,false,true]⟩ = some ⟨5, [false,true], [false] ++ rep [false,false,true,true] n ++ [false,false,true]⟩ := by rfl
theorem one1 (L R : List Bool) : run0 table 8 ⟨5, [false] ++ L, [false] ++ [false,false,true,true] ++ R⟩ = some ⟨5, [false] ++ [true,true,true,false] ++ L, [false] ++ R⟩ := by rfl
theorem h1 (n : Nat) : run0 table (8*n) ⟨5, [false,true], [false] ++ rep [false,false,true,true] n ++ [false,false,true]⟩ = some ⟨5, [false] ++ rep [true,true,true,false] n ++ [true], [false,false,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 5 [false] [false] [false,false,true,true] [true,true,true,false] 8 one1 n ([true]) ([false,false,true]))
theorem h2 (n : Nat) : run0 table 14 ⟨5, [false] ++ rep [true,true,true,false] n ++ [true], [false,false,false,true]⟩ = some ⟨1, [true,true,false,true,true,true,false] ++ rep [true,true,true,false] n ++ [true], []⟩ := by rfl
theorem one3 (L R : List Bool) : run0 table 6 ⟨1, [true,true,false,true,true,true,false] ++ [true,true,true,false] ++ L, [] ++ R⟩ = some ⟨1, [true,true,false,true,true,true,false] ++ L, [] ++ [true,false,false,true] ++ R⟩ := by rfl
theorem h3 (n : Nat) : run0 table (6*n) ⟨1, [true,true,false,true,true,true,false] ++ rep [true,true,true,false] n ++ [true], []⟩ = some ⟨1, [true,true,false,true,true,true,false,true], rep [true,false,false,true] n⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 1 [true,true,false,true,true,true,false] [] [true,true,true,false] [true,false,false,true] 6 one3 n ([true]) ([]))
theorem h4 (n : Nat) : run0 table 15 ⟨1, [true,true,false,true,true,true,false,true], rep [true,false,false,true] n⟩ = some ⟨4, [], [false,false,false,false,true,true,false,false,true] ++ rep [true,false,false,true] n⟩ := by rfl
theorem endEq (n : Nat) : ⟨4, [], [false,false,false,false,true,true,false,false,true] ++ rep [true,false,false,true] n⟩ = family (n+1) := by
  change (⟨4, [], [false,false,false,false,true,true,false,false,true] ++ rep [true,false,false,true] n⟩ : Z0) = (⟨4, [], [false,false,false,false,true,true] ++ rep [false,false,true,true] n ++ [false,false,true]⟩ : Z0)
  have hr : [false,false,false,false,true,true,false,false,true] ++ rep [true,false,false,true] n = [false,false,false,false,true,true] ++ rep [false,false,true,true] n ++ [false,false,true] := by
    calc
      _ = [false,false,false,false,true,true] ++ ([false,false,true] ++ rep [true,false,false,true] n) ++ [] := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
      _ = [false,false,false,false,true,true] ++ (rep [false,false,true,true] n ++ [false,false,true]) ++ [] := by rw [commute_rep [false,false,true] [true,false,false,true] [false,false,true,true] (by decide)]
      _ = _ := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
  rw [hr]
theorem growth (n : Nat) : run0 table (14*n+30) (family n) = some (family (n+1)) := by
  have h := h0 n
  have h := join0 h (h1 n)
  have h := join0 h (h2 n)
  have h := join0 h (h3 n)
  have h := join0 h (h4 n)
  rw [endEq] at h
  change run0 table _ (family n) = _ at h
  rw [show 14*n+30 = 1 + 8*n + 14 + 6*n + 15 by omega]
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 12 (fun n => 14*n+30) entry (by intro n; omega) growth m hm
#print axioms never
end M112

namespace M113
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,false,2⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨4, [true,true,true,true], rep [false,false,true,false,false,true] n ++ [false,false,true,false,false,true,false,false,false]⟩
theorem entry : run0 table 66 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem h0 (n : Nat) : run0 table 5 ⟨4, [true,true,true,true], rep [false,false,true,false,false,true] n ++ [false,false,true,false,false,true,false,false,false]⟩ = some ⟨3, [true,false], [false,false,true] ++ rep [false,false,true,false,false,true] n ++ [false,false,true,false,false,true,false,false,false]⟩ := by rfl
theorem one1 (L R : List Bool) : run0 table 26 ⟨3, [true,false] ++ L, [false,false,true] ++ [false,false,true,false,false,true] ++ R⟩ = some ⟨3, [true,false] ++ [true,true,true,true,true,true] ++ L, [false,false,true] ++ R⟩ := by rfl
theorem h1 (n : Nat) : run0 table (26*n) ⟨3, [true,false], [false,false,true] ++ rep [false,false,true,false,false,true] n ++ [false,false,true,false,false,true,false,false,false]⟩ = some ⟨3, [true,false] ++ rep [true,true,true,true,true,true] n, [false,false,true,false,false,true,false,false,true,false,false,false]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 3 [true,false] [false,false,true] [false,false,true,false,false,true] [true,true,true,true,true,true] 26 one1 n ([]) ([false,false,true,false,false,true,false,false,false]))
theorem h2 (n : Nat) : run0 table 74 ⟨3, [true,false] ++ rep [true,true,true,true,true,true] n, [false,false,true,false,false,true,false,false,true,false,false,false]⟩ = some ⟨2, [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ rep [true,true,true,true,true,true] n, [false]⟩ := by rfl
theorem one3 (L R : List Bool) : run0 table 6 ⟨2, [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ [true,true,true,true,true,true] ++ L, [] ++ R⟩ = some ⟨2, [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ L, [] ++ [true,false,false,true,false,false] ++ R⟩ := by rfl
theorem h3 (n : Nat) : run0 table (6*n) ⟨2, [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ rep [true,true,true,true,true,true] n, [false]⟩ = some ⟨2, [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true], rep [true,false,false,true,false,false] n ++ [false]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 2 [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true] [true,false,false,true,false,false] 6 one3 n ([]) ([false]))
theorem h4 (n : Nat) : run0 table 14 ⟨2, [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true], rep [true,false,false,true,false,false] n ++ [false]⟩ = some ⟨4, [true,true,true,true], [false,false,true,false,false,true,false,false,true,false,false,true,false,false] ++ rep [true,false,false,true,false,false] n ++ [false]⟩ := by rfl
theorem endEq (n : Nat) : ⟨4, [true,true,true,true], [false,false,true,false,false,true,false,false,true,false,false,true,false,false] ++ rep [true,false,false,true,false,false] n ++ [false]⟩ = family (n+1) := by
  change (⟨4, [true,true,true,true], [false,false,true,false,false,true,false,false,true,false,false,true,false,false] ++ rep [true,false,false,true,false,false] n ++ [false]⟩ : Z0) = (⟨4, [true,true,true,true], [false,false,true,false,false,true] ++ rep [false,false,true,false,false,true] n ++ [false,false,true,false,false,true,false,false,false]⟩ : Z0)
  have hr : [false,false,true,false,false,true,false,false,true,false,false,true,false,false] ++ rep [true,false,false,true,false,false] n ++ [false] = [false,false,true,false,false,true] ++ rep [false,false,true,false,false,true] n ++ [false,false,true,false,false,true,false,false,false] := by
    calc
      _ = [false,false,true,false,false,true] ++ ([false,false,true,false,false,true,false,false] ++ rep [true,false,false,true,false,false] n) ++ [false] := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
      _ = [false,false,true,false,false,true] ++ (rep [false,false,true,false,false,true] n ++ [false,false,true,false,false,true,false,false]) ++ [false] := by rw [commute_rep [false,false,true,false,false,true,false,false] [true,false,false,true,false,false] [false,false,true,false,false,true] (by decide)]
      _ = _ := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
  rw [hr]
theorem growth (n : Nat) : run0 table (32*n+93) (family n) = some (family (n+1)) := by
  have h := h0 n
  have h := join0 h (h1 n)
  have h := join0 h (h2 n)
  have h := join0 h (h3 n)
  have h := join0 h (h4 n)
  rw [endEq] at h
  change run0 table _ (family n) = _ at h
  rw [show 32*n+93 = 5 + 26*n + 74 + 6*n + 14 by omega]
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 66 (fun n => 32*n+93) entry (by intro n; omega) growth m hm
#print axioms never
end M113

namespace M116
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨0, [], [true] ++ rep [true,false,true,true,false,true] n ++ [true,false,false,true]⟩
theorem entry : run0 table 10 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem h0 (n : Nat) : run0 table 1 ⟨0, [], [true] ++ rep [true,false,true,true,false,true] n ++ [true,false,false,true]⟩ = some ⟨1, [true,true], rep [true,false,true,true,false,true] n ++ [true,false,false,true]⟩ := by rfl
theorem one1 (L R : List Bool) : run0 table 14 ⟨1, [true] ++ L, [] ++ [true,false,true,true,false,true] ++ R⟩ = some ⟨1, [true] ++ [true,false,true,true,false,true] ++ L, [] ++ R⟩ := by rfl
theorem h1 (n : Nat) : run0 table (14*n) ⟨1, [true,true], rep [true,false,true,true,false,true] n ++ [true,false,false,true]⟩ = some ⟨1, [true] ++ rep [true,false,true,true,false,true] n ++ [true], [true,false,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 1 [true] [] [true,false,true,true,false,true] [true,false,true,true,false,true] 14 one1 n ([true]) ([true,false,false,true]))
theorem h2 (n : Nat) : run0 table 9 ⟨1, [true] ++ rep [true,false,true,true,false,true] n ++ [true], [true,false,false,true]⟩ = some ⟨0, [true,true,false,true] ++ rep [true,false,true,true,false,true] n ++ [true], [false]⟩ := by rfl
theorem one3 (L R : List Bool) : run0 table 6 ⟨0, [true,true,false,true] ++ [true,false,true,true,false,true] ++ L, [] ++ R⟩ = some ⟨0, [true,true,false,true] ++ L, [] ++ [true,true,false,true,true,false] ++ R⟩ := by rfl
theorem h3 (n : Nat) : run0 table (6*n) ⟨0, [true,true,false,true] ++ rep [true,false,true,true,false,true] n ++ [true], [false]⟩ = some ⟨0, [true,true,false,true,true], rep [true,true,false,true,true,false] n ++ [false]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 0 [true,true,false,true] [] [true,false,true,true,false,true] [true,true,false,true,true,false] 6 one3 n ([true]) ([false]))
theorem h4 (n : Nat) : run0 table 7 ⟨0, [true,true,false,true,true], rep [true,true,false,true,true,false] n ++ [false]⟩ = some ⟨1, [true,true], [true,false,true,true,false] ++ rep [true,true,false,true,true,false] n ++ [false]⟩ := by rfl
theorem one5 (L R : List Bool) : run0 table 14 ⟨1, [true] ++ L, [true,false,true,true,false] ++ [true,true,false,true,true,false] ++ R⟩ = some ⟨1, [true] ++ [true,false,true,true,false,true] ++ L, [true,false,true,true,false] ++ R⟩ := by rfl
theorem h5 (n : Nat) : run0 table (14*n) ⟨1, [true,true], [true,false,true,true,false] ++ rep [true,true,false,true,true,false] n ++ [false]⟩ = some ⟨1, [true] ++ rep [true,false,true,true,false,true] n ++ [true], [true,false,true,true,false,false]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 1 [true] [true,false,true,true,false] [true,true,false,true,true,false] [true,false,true,true,false,true] 14 one5 n ([true]) ([false]))
theorem h6 (n : Nat) : run0 table 20 ⟨1, [true] ++ rep [true,false,true,true,false,true] n ++ [true], [true,false,true,true,false,false]⟩ = some ⟨0, [true,true,false,true,true,false,true] ++ rep [true,false,true,true,false,true] n ++ [true], [false,true]⟩ := by rfl
theorem one7 (L R : List Bool) : run0 table 6 ⟨0, [true,true,false,true,true,false,true] ++ [true,false,true,true,false,true] ++ L, [] ++ R⟩ = some ⟨0, [true,true,false,true,true,false,true] ++ L, [] ++ [true,true,false,true,true,false] ++ R⟩ := by rfl
theorem h7 (n : Nat) : run0 table (6*n) ⟨0, [true,true,false,true,true,false,true] ++ rep [true,false,true,true,false,true] n ++ [true], [false,true]⟩ = some ⟨0, [true,true,false,true,true,false,true,true], rep [true,true,false,true,true,false] n ++ [false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 0 [true,true,false,true,true,false,true] [] [true,false,true,true,false,true] [true,true,false,true,true,false] 6 one7 n ([true]) ([false,true]))
theorem h8 (n : Nat) : run0 table 9 ⟨0, [true,true,false,true,true,false,true,true], rep [true,true,false,true,true,false] n ++ [false,true]⟩ = some ⟨0, [], [true,true,false,true,true,false,true,true,false] ++ rep [true,true,false,true,true,false] n ++ [false,true]⟩ := by rfl
theorem endEq (n : Nat) : ⟨0, [], [true,true,false,true,true,false,true,true,false] ++ rep [true,true,false,true,true,false] n ++ [false,true]⟩ = family (n+1) := by
  change (⟨0, [], [true,true,false,true,true,false,true,true,false] ++ rep [true,true,false,true,true,false] n ++ [false,true]⟩ : Z0) = (⟨0, [], [true,true,false,true,true,false,true] ++ rep [true,false,true,true,false,true] n ++ [true,false,false,true]⟩ : Z0)
  have hr : [true,true,false,true,true,false,true,true,false] ++ rep [true,true,false,true,true,false] n ++ [false,true] = [true,true,false,true,true,false,true] ++ rep [true,false,true,true,false,true] n ++ [true,false,false,true] := by
    calc
      _ = [true,true,false,true,true,false,true] ++ ([true,false] ++ rep [true,true,false,true,true,false] n) ++ [false,true] := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
      _ = [true,true,false,true,true,false,true] ++ (rep [true,false,true,true,false,true] n ++ [true,false]) ++ [false,true] := by rw [commute_rep [true,false] [true,true,false,true,true,false] [true,false,true,true,false,true] (by decide)]
      _ = _ := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
  rw [hr]
theorem growth (n : Nat) : run0 table (40*n+46) (family n) = some (family (n+1)) := by
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
  rw [show 40*n+46 = 1 + 14*n + 9 + 6*n + 7 + 14*n + 20 + 6*n + 9 by omega]
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 10 (fun n => 40*n+46) entry (by intro n; omega) growth m hm
#print axioms never
end M116

namespace M118
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨1, [], [true,true,false,false] ++ rep [true,true,true,true] n ++ [true]⟩
theorem entry : run0 table 10 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem h0 (n : Nat) : run0 table 10 ⟨1, [], [true,true,false,false] ++ rep [true,true,true,true] n ++ [true]⟩ = some ⟨3, [true,false,true,true], [true,true] ++ rep [true,true,true,true] n ++ [true]⟩ := by rfl
theorem one1 (L R : List Bool) : run0 table 12 ⟨3, [true,false] ++ L, [true,true] ++ [true,true,true,true] ++ R⟩ = some ⟨3, [true,false] ++ [true,true,true,true] ++ L, [true,true] ++ R⟩ := by rfl
theorem h1 (n : Nat) : run0 table (12*n) ⟨3, [true,false,true,true], [true,true] ++ rep [true,true,true,true] n ++ [true]⟩ = some ⟨3, [true,false] ++ rep [true,true,true,true] n ++ [true,true], [true,true,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 3 [true,false] [true,true] [true,true,true,true] [true,true,true,true] 12 one1 n ([true,true]) ([true]))
theorem h2 (n : Nat) : run0 table 12 ⟨3, [true,false] ++ rep [true,true,true,true] n ++ [true,true], [true,true,true]⟩ = some ⟨3, [false,false,true,true,true,true] ++ rep [true,true,true,true] n ++ [true,true], []⟩ := by rfl
theorem one3 (L R : List Bool) : run0 table 60 ⟨3, [false,false,true,true,true,true] ++ [true,true,true,true] ++ L, [] ++ R⟩ = some ⟨3, [false,false,true,true,true,true] ++ L, [] ++ [true,true,true,true] ++ R⟩ := by rfl
theorem h3 (n : Nat) : run0 table (60*n) ⟨3, [false,false,true,true,true,true] ++ rep [true,true,true,true] n ++ [true,true], []⟩ = some ⟨3, [false,false,true,true,true,true,true,true], rep [true,true,true,true] n⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 3 [false,false,true,true,true,true] [] [true,true,true,true] [true,true,true,true] 60 one3 n ([true,true]) ([]))
theorem h4 (n : Nat) : run0 table 67 ⟨3, [false,false,true,true,true,true,true,true], rep [true,true,true,true] n⟩ = some ⟨1, [], [true,true,false,false,true,true,true,true,true] ++ rep [true,true,true,true] n⟩ := by rfl
theorem endEq (n : Nat) : ⟨1, [], [true,true,false,false,true,true,true,true,true] ++ rep [true,true,true,true] n⟩ = family (n+1) := by
  change (⟨1, [], [true,true,false,false,true,true,true,true,true] ++ rep [true,true,true,true] n⟩ : Z0) = (⟨1, [], [true,true,false,false,true,true,true,true] ++ rep [true,true,true,true] n ++ [true]⟩ : Z0)
  have hr : [true,true,false,false,true,true,true,true,true] ++ rep [true,true,true,true] n = [true,true,false,false,true,true,true,true] ++ rep [true,true,true,true] n ++ [true] := by
    calc
      _ = [true,true,false,false,true,true,true,true] ++ ([true] ++ rep [true,true,true,true] n) ++ [] := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
      _ = [true,true,false,false,true,true,true,true] ++ (rep [true,true,true,true] n ++ [true]) ++ [] := by rw [commute_rep [true] [true,true,true,true] [true,true,true,true] (by decide)]
      _ = _ := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
  rw [hr]
theorem growth (n : Nat) : run0 table (72*n+89) (family n) = some (family (n+1)) := by
  have h := h0 n
  have h := join0 h (h1 n)
  have h := join0 h (h2 n)
  have h := join0 h (h3 n)
  have h := join0 h (h4 n)
  rw [endEq] at h
  change run0 table _ (family n) = _ at h
  rw [show 72*n+89 = 10 + 12*n + 12 + 60*n + 67 by omega]
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 10 (fun n => 72*n+89) entry (by intro n; omega) growth m hm
#print axioms never
end M118

namespace M603
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨3, [true], [true] ++ rep [true,true,false,true,true,false,true,true,false] n ++ [true,true,false,true]⟩
theorem entry : run0 table 14 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem h0 (n : Nat) : run0 table 4 ⟨3, [true], [true] ++ rep [true,true,false,true,true,false,true,true,false] n ++ [true,true,false,true]⟩ = some ⟨1, [true,false], [false] ++ rep [true,true,false,true,true,false,true,true,false] n ++ [true,true,false,true]⟩ := by rfl
theorem one1 (L R : List Bool) : run0 table 15 ⟨1, [true] ++ L, [false] ++ [true,true,false,true,true,false,true,true,false] ++ R⟩ = some ⟨1, [true] ++ [false,true,false,false,true,false,false,true,false] ++ L, [false] ++ R⟩ := by rfl
theorem h1 (n : Nat) : run0 table (15*n) ⟨1, [true,false], [false] ++ rep [true,true,false,true,true,false,true,true,false] n ++ [true,true,false,true]⟩ = some ⟨1, [true] ++ rep [false,true,false,false,true,false,false,true,false] n ++ [false], [false,true,true,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 1 [true] [false] [true,true,false,true,true,false,true,true,false] [false,true,false,false,true,false,false,true,false] 15 one1 n ([false]) ([true,true,false,true]))
theorem h2 (n : Nat) : run0 table 41 ⟨1, [true] ++ rep [false,true,false,false,true,false,false,true,false] n ++ [false], [false,true,true,false,true]⟩ = some ⟨2, [true,true,true,false,false,true,false,false,true,false] ++ rep [false,true,false,false,true,false,false,true,false] n ++ [false], []⟩ := by rfl
theorem one3 (L R : List Bool) : run0 table 27 ⟨2, [true,true,true,false,false,true,false,false,true,false] ++ [false,true,false,false,true,false,false,true,false] ++ L, [] ++ R⟩ = some ⟨2, [true,true,true,false,false,true,false,false,true,false] ++ L, [] ++ [true,true,false,true,true,false,true,true,false] ++ R⟩ := by rfl
theorem h3 (n : Nat) : run0 table (27*n) ⟨2, [true,true,true,false,false,true,false,false,true,false] ++ rep [false,true,false,false,true,false,false,true,false] n ++ [false], []⟩ = some ⟨2, [true,true,true,false,false,true,false,false,true,false,false], rep [true,true,false,true,true,false,true,true,false] n⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 2 [true,true,true,false,false,true,false,false,true,false] [] [false,true,false,false,true,false,false,true,false] [true,true,false,true,true,false,true,true,false] 27 one3 n ([false]) ([]))
theorem h4 (n : Nat) : run0 table 30 ⟨2, [true,true,true,false,false,true,false,false,true,false,false], rep [true,true,false,true,true,false,true,true,false] n⟩ = some ⟨1, [true,false], [false,true,true,false,true,true,false,true,true,false] ++ rep [true,true,false,true,true,false,true,true,false] n⟩ := by rfl
theorem one5 (L R : List Bool) : run0 table 15 ⟨1, [true] ++ L, [false,true,true,false,true,true,false,true,true,false] ++ [true,true,false,true,true,false,true,true,false] ++ R⟩ = some ⟨1, [true] ++ [false,true,false,false,true,false,false,true,false] ++ L, [false,true,true,false,true,true,false,true,true,false] ++ R⟩ := by rfl
theorem h5 (n : Nat) : run0 table (15*n) ⟨1, [true,false], [false,true,true,false,true,true,false,true,true,false] ++ rep [true,true,false,true,true,false,true,true,false] n⟩ = some ⟨1, [true] ++ rep [false,true,false,false,true,false,false,true,false] n ++ [false], [false,true,true,false,true,true,false,true,true,false]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 1 [true] [false,true,true,false,true,true,false,true,true,false] [true,true,false,true,true,false,true,true,false] [false,true,false,false,true,false,false,true,false] 15 one5 n ([false]) ([]))
theorem h6 (n : Nat) : run0 table 19 ⟨1, [true] ++ rep [false,true,false,false,true,false,false,true,false] n ++ [false], [false,true,true,false,true,true,false,true,true,false]⟩ = some ⟨3, [false,false,true,true,false,false,true,false,false,true,false,false,true,false] ++ rep [false,true,false,false,true,false,false,true,false] n ++ [false], []⟩ := by rfl
theorem one7 (L R : List Bool) : run0 table 27 ⟨3, [false,false,true,true,false,false,true,false,false,true,false,false,true,false] ++ [false,true,false,false,true,false,false,true,false] ++ L, [] ++ R⟩ = some ⟨3, [false,false,true,true,false,false,true,false,false,true,false,false,true,false] ++ L, [] ++ [true,false,true,true,false,true,true,false,true] ++ R⟩ := by rfl
theorem h7 (n : Nat) : run0 table (27*n) ⟨3, [false,false,true,true,false,false,true,false,false,true,false,false,true,false] ++ rep [false,true,false,false,true,false,false,true,false] n ++ [false], []⟩ = some ⟨3, [false,false,true,true,false,false,true,false,false,true,false,false,true,false,false], rep [true,false,true,true,false,true,true,false,true] n⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 3 [false,false,true,true,false,false,true,false,false,true,false,false,true,false] [] [false,true,false,false,true,false,false,true,false] [true,false,true,true,false,true,true,false,true] 27 one7 n ([false]) ([]))
theorem h8 (n : Nat) : run0 table 38 ⟨3, [false,false,true,true,false,false,true,false,false,true,false,false,true,false,false], rep [true,false,true,true,false,true,true,false,true] n⟩ = some ⟨3, [true], [true,true,true,false,true,true,false,true,true,false,true,true,false,true] ++ rep [true,false,true,true,false,true,true,false,true] n⟩ := by rfl
theorem endEq (n : Nat) : ⟨3, [true], [true,true,true,false,true,true,false,true,true,false,true,true,false,true] ++ rep [true,false,true,true,false,true,true,false,true] n⟩ = family (n+1) := by
  change (⟨3, [true], [true,true,true,false,true,true,false,true,true,false,true,true,false,true] ++ rep [true,false,true,true,false,true,true,false,true] n⟩ : Z0) = (⟨3, [true], [true,true,true,false,true,true,false,true,true,false] ++ rep [true,true,false,true,true,false,true,true,false] n ++ [true,true,false,true]⟩ : Z0)
  have hr : [true,true,true,false,true,true,false,true,true,false,true,true,false,true] ++ rep [true,false,true,true,false,true,true,false,true] n = [true,true,true,false,true,true,false,true,true,false] ++ rep [true,true,false,true,true,false,true,true,false] n ++ [true,true,false,true] := by
    calc
      _ = [true,true,true,false,true,true,false,true,true,false] ++ ([true,true,false,true] ++ rep [true,false,true,true,false,true,true,false,true] n) ++ [] := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
      _ = [true,true,true,false,true,true,false,true,true,false] ++ (rep [true,true,false,true,true,false,true,true,false] n ++ [true,true,false,true]) ++ [] := by rw [commute_rep [true,true,false,true] [true,false,true,true,false,true,true,false,true] [true,true,false,true,true,false,true,true,false] (by decide)]
      _ = _ := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
  rw [hr]
theorem growth (n : Nat) : run0 table (84*n+132) (family n) = some (family (n+1)) := by
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
  rw [show 84*n+132 = 4 + 15*n + 41 + 27*n + 30 + 15*n + 19 + 27*n + 38 by omega]
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 14 (fun n => 84*n+132) entry (by intro n; omega) growth m hm
#print axioms never
end M603

namespace M604
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨5, [], [false] ++ rep [false,false] n ++ [true,false,true] ++ rep [true] n⟩
theorem entry : run0 table 9 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem h0 (n : Nat) : run0 table 9 ⟨5, [], [false] ++ rep [false,false] n ++ [true,false,true] ++ rep [true] n⟩ = some ⟨2, [true,false], [false,true] ++ rep [false,false] n ++ [true,false,true] ++ rep [true] n⟩ := by rfl
theorem one1 (L R : List Bool) : run0 table 12 ⟨2, [true,false] ++ L, [false,true] ++ [false,false] ++ R⟩ = some ⟨2, [true,false] ++ [true,true] ++ L, [false,true] ++ R⟩ := by rfl
theorem h1 (n : Nat) : run0 table (12*n) ⟨2, [true,false], [false,true] ++ rep [false,false] n ++ [true,false,true] ++ rep [true] n⟩ = some ⟨2, [true,false] ++ rep [true,true] n, [false,true,true,false,true] ++ rep [true] n⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 2 [true,false] [false,true] [false,false] [true,true] 12 one1 n ([]) ([true,false,true] ++ rep [true] n))
theorem h2 (n : Nat) : run0 table 18 ⟨2, [true,false] ++ rep [true,true] n, [false,true,true,false,true] ++ rep [true] n⟩ = some ⟨5, [true,true] ++ rep [true,true] n, [false,true,false,true,true] ++ rep [true] n⟩ := by rfl
theorem one3 (L R : List Bool) : run0 table 2 ⟨5, [true,true] ++ [true,true] ++ L, [] ++ R⟩ = some ⟨5, [true,true] ++ L, [] ++ [false,false] ++ R⟩ := by rfl
theorem h3 (n : Nat) : run0 table (2*n) ⟨5, [true,true] ++ rep [true,true] n, [false,true,false,true,true] ++ rep [true] n⟩ = some ⟨5, [true,true], rep [false,false] n ++ [false,true,false,true,true] ++ rep [true] n⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 5 [true,true] [] [true,true] [false,false] 2 one3 n ([]) ([false,true,false,true,true] ++ rep [true] n))
theorem h4 (n : Nat) : run0 table 2 ⟨5, [true,true], rep [false,false] n ++ [false,true,false,true,true] ++ rep [true] n⟩ = some ⟨5, [], [false,false] ++ rep [false,false] n ++ [false,true,false,true,true] ++ rep [true] n⟩ := by rfl
theorem endEq (n : Nat) : ⟨5, [], [false,false] ++ rep [false,false] n ++ [false,true,false,true,true] ++ rep [true] n⟩ = family (n+1) := by
  simp only [family,rep,List.append_assoc]
  have h := commute_rep [false] [false,false] [false,false] (by decide) n
  have hr : [false,false] ++ rep [false,false] n ++ [false,true,false,true,true] = [false,false,false] ++ rep [false,false] n ++ [true,false,true,true] := by
    calc
      _ = [false,false] ++ (rep [false,false] n ++ [false]) ++ [true,false,true,true] := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
      _ = [false,false] ++ ([false] ++ rep [false,false] n) ++ [true,false,true,true] := by rw [h]
      _ = _ := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
  have hh := congrArg (fun z : List Bool => z ++ rep [true] n) hr
  simpa only [List.append_assoc,List.cons_append,List.nil_append] using congrArg (fun z : List Bool => Z0.mk 5 ([]) z) hh
theorem growth (n : Nat) : run0 table (14*n+29) (family n) = some (family (n+1)) := by
  have h := h0 n
  have h := join0 h (h1 n)
  have h := join0 h (h2 n)
  have h := join0 h (h3 n)
  have h := join0 h (h4 n)
  rw [endEq] at h
  change run0 table _ (family n) = _ at h
  rw [show 14*n+29 = 9 + 12*n + 18 + 2*n + 2 by omega]
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 9 (fun n => 14*n+29) entry (by intro n; omega) growth m hm
#print axioms never
end M604

namespace M607
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨0, [], [true] ++ rep [false,true,true,false,true,true] n ++ [false,true,false,true]⟩
theorem entry : run0 table 10 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem h0 (n : Nat) : run0 table 1 ⟨0, [], [true] ++ rep [false,true,true,false,true,true] n ++ [false,true,false,true]⟩ = some ⟨1, [true,true], rep [false,true,true,false,true,true] n ++ [false,true,false,true]⟩ := by rfl
theorem one1 (L R : List Bool) : run0 table 10 ⟨1, [true] ++ L, [] ++ [false,true,true,false,true,true] ++ R⟩ = some ⟨1, [true] ++ [true,false,true,true,false,true] ++ L, [] ++ R⟩ := by rfl
theorem h1 (n : Nat) : run0 table (10*n) ⟨1, [true,true], rep [false,true,true,false,true,true] n ++ [false,true,false,true]⟩ = some ⟨1, [true] ++ rep [true,false,true,true,false,true] n ++ [true], [false,true,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 1 [true] [] [false,true,true,false,true,true] [true,false,true,true,false,true] 10 one1 n ([true]) ([false,true,false,true]))
theorem h2 (n : Nat) : run0 table 7 ⟨1, [true] ++ rep [true,false,true,true,false,true] n ++ [true], [false,true,false,true]⟩ = some ⟨0, [true,true,false,true] ++ rep [true,false,true,true,false,true] n ++ [true], [false]⟩ := by rfl
theorem one3 (L R : List Bool) : run0 table 6 ⟨0, [true,true,false,true] ++ [true,false,true,true,false,true] ++ L, [] ++ R⟩ = some ⟨0, [true,true,false,true] ++ L, [] ++ [true,false,true,true,false,true] ++ R⟩ := by rfl
theorem h3 (n : Nat) : run0 table (6*n) ⟨0, [true,true,false,true] ++ rep [true,false,true,true,false,true] n ++ [true], [false]⟩ = some ⟨0, [true,true,false,true,true], rep [true,false,true,true,false,true] n ++ [false]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 0 [true,true,false,true] [] [true,false,true,true,false,true] [true,false,true,true,false,true] 6 one3 n ([true]) ([false]))
theorem h4 (n : Nat) : run0 table 7 ⟨0, [true,true,false,true,true], rep [true,false,true,true,false,true] n ++ [false]⟩ = some ⟨1, [true,true], [false,true,true,false,true] ++ rep [true,false,true,true,false,true] n ++ [false]⟩ := by rfl
theorem one5 (L R : List Bool) : run0 table 10 ⟨1, [true] ++ L, [false,true,true,false,true] ++ [true,false,true,true,false,true] ++ R⟩ = some ⟨1, [true] ++ [true,false,true,true,false,true] ++ L, [false,true,true,false,true] ++ R⟩ := by rfl
theorem h5 (n : Nat) : run0 table (10*n) ⟨1, [true,true], [false,true,true,false,true] ++ rep [true,false,true,true,false,true] n ++ [false]⟩ = some ⟨1, [true] ++ rep [true,false,true,true,false,true] n ++ [true], [false,true,true,false,true,false]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 1 [true] [false,true,true,false,true] [true,false,true,true,false,true] [true,false,true,true,false,true] 10 one5 n ([true]) ([false]))
theorem h6 (n : Nat) : run0 table 16 ⟨1, [true] ++ rep [true,false,true,true,false,true] n ++ [true], [false,true,true,false,true,false]⟩ = some ⟨0, [true,true,false,true,true,false,true] ++ rep [true,false,true,true,false,true] n ++ [true], [false,true]⟩ := by rfl
theorem one7 (L R : List Bool) : run0 table 6 ⟨0, [true,true,false,true,true,false,true] ++ [true,false,true,true,false,true] ++ L, [] ++ R⟩ = some ⟨0, [true,true,false,true,true,false,true] ++ L, [] ++ [true,false,true,true,false,true] ++ R⟩ := by rfl
theorem h7 (n : Nat) : run0 table (6*n) ⟨0, [true,true,false,true,true,false,true] ++ rep [true,false,true,true,false,true] n ++ [true], [false,true]⟩ = some ⟨0, [true,true,false,true,true,false,true,true], rep [true,false,true,true,false,true] n ++ [false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 0 [true,true,false,true,true,false,true] [] [true,false,true,true,false,true] [true,false,true,true,false,true] 6 one7 n ([true]) ([false,true]))
theorem h8 (n : Nat) : run0 table 9 ⟨0, [true,true,false,true,true,false,true,true], rep [true,false,true,true,false,true] n ++ [false,true]⟩ = some ⟨0, [], [true,false,true,true,false,true,true,false,true] ++ rep [true,false,true,true,false,true] n ++ [false,true]⟩ := by rfl
theorem endEq (n : Nat) : ⟨0, [], [true,false,true,true,false,true,true,false,true] ++ rep [true,false,true,true,false,true] n ++ [false,true]⟩ = family (n+1) := by
  change (⟨0, [], [true,false,true,true,false,true,true,false,true] ++ rep [true,false,true,true,false,true] n ++ [false,true]⟩ : Z0) = (⟨0, [], [true,false,true,true,false,true,true] ++ rep [false,true,true,false,true,true] n ++ [false,true,false,true]⟩ : Z0)
  have hr : [true,false,true,true,false,true,true,false,true] ++ rep [true,false,true,true,false,true] n ++ [false,true] = [true,false,true,true,false,true,true] ++ rep [false,true,true,false,true,true] n ++ [false,true,false,true] := by
    calc
      _ = [true,false,true,true,false,true,true] ++ ([false,true] ++ rep [true,false,true,true,false,true] n) ++ [false,true] := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
      _ = [true,false,true,true,false,true,true] ++ (rep [false,true,true,false,true,true] n ++ [false,true]) ++ [false,true] := by rw [commute_rep [false,true] [true,false,true,true,false,true] [false,true,true,false,true,true] (by decide)]
      _ = _ := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
  rw [hr]
theorem growth (n : Nat) : run0 table (32*n+40) (family n) = some (family (n+1)) := by
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
  rw [show 32*n+40 = 1 + 10*n + 7 + 6*n + 7 + 10*n + 16 + 6*n + 9 by omega]
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 10 (fun n => 32*n+40) entry (by intro n; omega) growth m hm
#print axioms never
end M607

namespace M609
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,false,3⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨0, [], [false,false] ++ rep [true,false,true,false] n ++ [true,false,true]⟩
theorem entry : run0 table 12 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem h0 (n : Nat) : run0 table 2 ⟨0, [], [false,false] ++ rep [true,false,true,false] n ++ [true,false,true]⟩ = some ⟨2, [false,true,true], rep [true,false,true,false] n ++ [true,false,true]⟩ := by rfl
theorem one1 (L R : List Bool) : run0 table 4 ⟨2, [false] ++ L, [] ++ [true,false,true,false] ++ R⟩ = some ⟨2, [false] ++ [true,false,true,false] ++ L, [] ++ R⟩ := by rfl
theorem h1 (n : Nat) : run0 table (4*n) ⟨2, [false,true,true], rep [true,false,true,false] n ++ [true,false,true]⟩ = some ⟨2, [false] ++ rep [true,false,true,false] n ++ [true,true], [true,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 2 [false] [] [true,false,true,false] [true,false,true,false] 4 one1 n ([true,true]) ([true,false,true]))
theorem h2 (n : Nat) : run0 table 6 ⟨2, [false] ++ rep [true,false,true,false] n ++ [true,true], [true,false,true]⟩ = some ⟨3, [false,true,false,true,false] ++ rep [true,false,true,false] n ++ [true,true], [true]⟩ := by rfl
theorem one3 (L R : List Bool) : run0 table 6 ⟨3, [false,true,false,true,false] ++ [true,false,true,false] ++ L, [] ++ R⟩ = some ⟨3, [false,true,false,true,false] ++ L, [] ++ [true,false,true,false] ++ R⟩ := by rfl
theorem h3 (n : Nat) : run0 table (6*n) ⟨3, [false,true,false,true,false] ++ rep [true,false,true,false] n ++ [true,true], [true]⟩ = some ⟨3, [false,true,false,true,false,true,true], rep [true,false,true,false] n ++ [true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 3 [false,true,false,true,false] [] [true,false,true,false] [true,false,true,false] 6 one3 n ([true,true]) ([true]))
theorem h4 (n : Nat) : run0 table 14 ⟨3, [false,true,false,true,false,true,true], rep [true,false,true,false] n ++ [true]⟩ = some ⟨0, [], [false,false,true,false,true,false,true,false] ++ rep [true,false,true,false] n ++ [true]⟩ := by rfl
theorem endEq (n : Nat) : ⟨0, [], [false,false,true,false,true,false,true,false] ++ rep [true,false,true,false] n ++ [true]⟩ = family (n+1) := by
  change (⟨0, [], [false,false,true,false,true,false,true,false] ++ rep [true,false,true,false] n ++ [true]⟩ : Z0) = (⟨0, [], [false,false,true,false,true,false] ++ rep [true,false,true,false] n ++ [true,false,true]⟩ : Z0)
  have hr : [false,false,true,false,true,false,true,false] ++ rep [true,false,true,false] n ++ [true] = [false,false,true,false,true,false] ++ rep [true,false,true,false] n ++ [true,false,true] := by
    calc
      _ = [false,false,true,false,true,false] ++ ([true,false] ++ rep [true,false,true,false] n) ++ [true] := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
      _ = [false,false,true,false,true,false] ++ (rep [true,false,true,false] n ++ [true,false]) ++ [true] := by rw [commute_rep [true,false] [true,false,true,false] [true,false,true,false] (by decide)]
      _ = _ := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
  rw [hr]
theorem growth (n : Nat) : run0 table (10*n+22) (family n) = some (family (n+1)) := by
  have h := h0 n
  have h := join0 h (h1 n)
  have h := join0 h (h2 n)
  have h := join0 h (h3 n)
  have h := join0 h (h4 n)
  rw [endEq] at h
  change run0 table _ (family n) = _ at h
  rw [show 10*n+22 = 2 + 4*n + 6 + 6*n + 14 by omega]
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 12 (fun n => 10*n+22) entry (by intro n; omega) growth m hm
#print axioms never
end M609

namespace M610
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,2⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨4, [true], rep [true,true] n ++ [true,true,true,false,true]⟩
theorem entry : run0 table 27 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem h0 (n : Nat) : run0 table 2 ⟨4, [true], rep [true,true] n ++ [true,true,true,false,true]⟩ = some ⟨1, [true,true], rep [true,true] n ++ [true,true,true,false,true]⟩ := by rfl
theorem one1 (L R : List Bool) : run0 table 6 ⟨1, [true] ++ L, [] ++ [true,true] ++ R⟩ = some ⟨1, [true] ++ [true,true] ++ L, [] ++ R⟩ := by rfl
theorem h1 (n : Nat) : run0 table (6*n) ⟨1, [true,true], rep [true,true] n ++ [true,true,true,false,true]⟩ = some ⟨1, [true] ++ rep [true,true] n ++ [true], [true,true,true,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 1 [true] [] [true,true] [true,true] 6 one1 n ([true]) ([true,true,true,false,true]))
theorem h2 (n : Nat) : run0 table 20 ⟨1, [true] ++ rep [true,true] n ++ [true], [true,true,true,false,true]⟩ = some ⟨0, [true,true,true,true,true] ++ rep [true,true] n ++ [true], [false,true]⟩ := by rfl
theorem one3 (L R : List Bool) : run0 table 2 ⟨0, [true,true,true,true,true] ++ [true,true] ++ L, [] ++ R⟩ = some ⟨0, [true,true,true,true,true] ++ L, [] ++ [true,true] ++ R⟩ := by rfl
theorem h3 (n : Nat) : run0 table (2*n) ⟨0, [true,true,true,true,true] ++ rep [true,true] n ++ [true], [false,true]⟩ = some ⟨0, [true,true,true,true,true,true], rep [true,true] n ++ [false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 0 [true,true,true,true,true] [] [true,true] [true,true] 2 one3 n ([true]) ([false,true]))
theorem h4 (n : Nat) : run0 table 5 ⟨0, [true,true,true,true,true,true], rep [true,true] n ++ [false,true]⟩ = some ⟨4, [true], [true,true,true,true,true] ++ rep [true,true] n ++ [false,true]⟩ := by rfl
theorem endEq (n : Nat) : ⟨4, [true], [true,true,true,true,true] ++ rep [true,true] n ++ [false,true]⟩ = family (n+1) := by
  change (⟨4, [true], [true,true,true,true,true] ++ rep [true,true] n ++ [false,true]⟩ : Z0) = (⟨4, [true], [true,true] ++ rep [true,true] n ++ [true,true,true,false,true]⟩ : Z0)
  have hr : [true,true,true,true,true] ++ rep [true,true] n ++ [false,true] = [true,true] ++ rep [true,true] n ++ [true,true,true,false,true] := by
    calc
      _ = [true,true] ++ ([true,true,true] ++ rep [true,true] n) ++ [false,true] := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
      _ = [true,true] ++ (rep [true,true] n ++ [true,true,true]) ++ [false,true] := by rw [commute_rep [true,true,true] [true,true] [true,true] (by decide)]
      _ = _ := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
  rw [hr]
theorem growth (n : Nat) : run0 table (8*n+27) (family n) = some (family (n+1)) := by
  have h := h0 n
  have h := join0 h (h1 n)
  have h := join0 h (h2 n)
  have h := join0 h (h3 n)
  have h := join0 h (h4 n)
  rw [endEq] at h
  change run0 table _ (family n) = _ at h
  rw [show 8*n+27 = 2 + 6*n + 20 + 2*n + 5 by omega]
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 27 (fun n => 8*n+27) entry (by intro n; omega) growth m hm
#print axioms never
end M610

namespace M616
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,true,3⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨1, [], [false,false] ++ rep [false,false,false,false] n ++ [false,false,true]⟩
theorem entry : run0 table 12 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem h0 (n : Nat) : run0 table 8 ⟨1, [], [false,false] ++ rep [false,false,false,false] n ++ [false,false,true]⟩ = some ⟨3, [true,true], [false,true] ++ rep [false,false,false,false] n ++ [false,false,true]⟩ := by rfl
theorem one1 (L R : List Bool) : run0 table 20 ⟨3, [true] ++ L, [false,true] ++ [false,false,false,false] ++ R⟩ = some ⟨3, [true] ++ [true,true,true,true] ++ L, [false,true] ++ R⟩ := by rfl
theorem h1 (n : Nat) : run0 table (20*n) ⟨3, [true,true], [false,true] ++ rep [false,false,false,false] n ++ [false,false,true]⟩ = some ⟨3, [true] ++ rep [true,true,true,true] n ++ [true], [false,true,false,false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepR table 3 [true] [false,true] [false,false,false,false] [true,true,true,true] 20 one1 n ([true]) ([false,false,true]))
theorem h2 (n : Nat) : run0 table 24 ⟨3, [true] ++ rep [true,true,true,true] n ++ [true], [false,true,false,false,true]⟩ = some ⟨5, [true,true,true,true,true] ++ rep [true,true,true,true] n ++ [true], [false,true]⟩ := by rfl
theorem one3 (L R : List Bool) : run0 table 4 ⟨5, [true,true,true,true,true] ++ [true,true,true,true] ++ L, [] ++ R⟩ = some ⟨5, [true,true,true,true,true] ++ L, [] ++ [false,false,false,false] ++ R⟩ := by rfl
theorem h3 (n : Nat) : run0 table (4*n) ⟨5, [true,true,true,true,true] ++ rep [true,true,true,true] n ++ [true], [false,true]⟩ = some ⟨5, [true,true,true,true,true,true], rep [false,false,false,false] n ++ [false,true]⟩ := by
  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (sweepL table 5 [true,true,true,true,true] [] [true,true,true,true] [false,false,false,false] 4 one3 n ([true]) ([false,true]))
theorem h4 (n : Nat) : run0 table 7 ⟨5, [true,true,true,true,true,true], rep [false,false,false,false] n ++ [false,true]⟩ = some ⟨1, [], [false,false,false,false,false,false,false] ++ rep [false,false,false,false] n ++ [false,true]⟩ := by rfl
theorem endEq (n : Nat) : ⟨1, [], [false,false,false,false,false,false,false] ++ rep [false,false,false,false] n ++ [false,true]⟩ = family (n+1) := by
  change (⟨1, [], [false,false,false,false,false,false,false] ++ rep [false,false,false,false] n ++ [false,true]⟩ : Z0) = (⟨1, [], [false,false,false,false,false,false] ++ rep [false,false,false,false] n ++ [false,false,true]⟩ : Z0)
  have hr : [false,false,false,false,false,false,false] ++ rep [false,false,false,false] n ++ [false,true] = [false,false,false,false,false,false] ++ rep [false,false,false,false] n ++ [false,false,true] := by
    calc
      _ = [false,false,false,false,false,false] ++ ([false] ++ rep [false,false,false,false] n) ++ [false,true] := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
      _ = [false,false,false,false,false,false] ++ (rep [false,false,false,false] n ++ [false]) ++ [false,true] := by rw [commute_rep [false] [false,false,false,false] [false,false,false,false] (by decide)]
      _ = _ := by simp only [List.append_assoc,List.append_nil,List.nil_append] <;> rfl
  rw [hr]
theorem growth (n : Nat) : run0 table (24*n+39) (family n) = some (family (n+1)) := by
  have h := h0 n
  have h := join0 h (h1 n)
  have h := join0 h (h2 n)
  have h := join0 h (h3 n)
  have h := join0 h (h4 n)
  rw [endEq] at h
  change run0 table _ (family n) = _ at h
  rw [show 24*n+39 = 8 + 20*n + 24 + 4*n + 7 by omega]
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 12 (fun n => 24*n+39) entry (by intro n; omega) growth m hm
#print axioms never
end M616

end BB6.Agent7Raw49AutoSweeps
