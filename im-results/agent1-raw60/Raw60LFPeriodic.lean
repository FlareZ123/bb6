import SweepPumping

set_option maxRecDepth 100000

set_option maxHeartbeats 0

set_option linter.unusedVariables false

namespace BB6.Agent1Raw60LFPeriodic

open BB6Coverage BB6Coverage.Agent31Pump

open Lean in
macro "w!" s:str : term => do
  let xs ← s.getString.toList.toArray.mapM fun c => if c == '1' then `(true) else `(false)
  `([$[$xs],*])

inductive V | a | b | c deriving DecidableEq

def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => match v with | .a => some (some ⟨false,true,4⟩) | .b => some (some ⟨false,true,0⟩) | .c => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => match v with | .a => none | .b => some (some ⟨false,true,4⟩) | .c => some (some ⟨true,false,1⟩)
  | 5,true => match v with | .a => some (some ⟨true,false,1⟩) | .b => some (some ⟨true,false,1⟩) | .c => some (some ⟨false,true,0⟩)
  | _,_ => none

def family (n : Nat) : Z0 := ⟨1,[],((w! "0011")) ++ (rep (w! "00011001100011") (n)) ++ ((w! "0001100110001100"))⟩

def entryCost (v : V) : Nat := match v with | .a => 289 | .b => 297 | .c => 333

theorem entry (v : V) : run0 (table v) (entryCost v) ⟨0,[],[]⟩ = some (family 0) := by cases v <;> rfl

def K0 (v : V) : Nat := match v with | .a => 23 | .b => 23 | .c => 29

theorem phase0 (v : V) (n : Nat) : run0 (table v) (K0 v) ⟨1,[],((w! "0011")) ++ (rep (w! "00011001100011") (n)) ++ ((w! "0001100110001100"))⟩ = some ⟨1,(w! "011"),((w! "011")) ++ (rep (w! "00011001100011") (n)) ++ ((w! "0001100110001100"))⟩ := by cases v <;> rfl

def K1 (v : V) : Nat := match v with | .a => 14 | .b => 16 | .c => 14

theorem local1 (v : V) (L R : List Bool) : run0 (table v) (K1 v) ⟨1,((w! "0")) ++ (L),((w! "011")) ++ ((w! "00011001100011")) ++ (R)⟩ = some ⟨1,((w! "0")) ++ ((w! "11011110111101")) ++ (L),((w! "011")) ++ (R)⟩ := by cases v <;> rfl

theorem phase1 (v : V) (n : Nat) : run0 (table v) (K1 v*n) ⟨1,(w! "011"),((w! "011")) ++ (rep (w! "00011001100011") (n)) ++ ((w! "0001100110001100"))⟩ = some ⟨1,((w! "0")) ++ (rep (w! "11011110111101") (n)) ++ ((w! "11")),(w! "0110001100110001100")⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR (table v) 1 (w! "0") (w! "011") (w! "00011001100011") (w! "11011110111101") (K1 v) (local1 v) n (w! "11") (w! "0001100110001100")

def K2 (v : V) : Nat := match v with | .a => 27 | .b => 29 | .c => 29

theorem phase2 (v : V) (n : Nat) : run0 (table v) (K2 v) ⟨1,((w! "0")) ++ (rep (w! "11011110111101") (n)) ++ ((w! "11")),(w! "0110001100110001100")⟩ = some ⟨1,((w! "11110111011110111101")) ++ (rep (w! "11011110111101") (n)) ++ ((w! "11")),(w! "11")⟩ := by cases v <;> rfl

def K3 (v : V) : Nat := match v with | .a => 38 | .b => 38 | .c => 44

theorem local3 (v : V) (L R : List Bool) : run0 (table v) (K3 v) ⟨1,((w! "11110111011110111101")) ++ ((w! "11011110111101")) ++ (L),(R)⟩ = some ⟨1,((w! "11110111011110111101")) ++ (L),((w! "01100011001100")) ++ (R)⟩ := by cases v <;> rfl

theorem phase3 (v : V) (n : Nat) : run0 (table v) (K3 v*n) ⟨1,((w! "11110111011110111101")) ++ (rep (w! "11011110111101") (n)) ++ ((w! "11")),(w! "11")⟩ = some ⟨1,(w! "1111011101111011110111"),(rep (w! "01100011001100") (n)) ++ ((w! "11"))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL (table v) 1 (w! "11110111011110111101") [] (w! "11011110111101") (w! "01100011001100") (K3 v) (local3 v) n (w! "11") (w! "11")

def K4 (v : V) : Nat := match v with | .a => 64 | .b => 64 | .c => 74

theorem phase4 (v : V) (n : Nat) : run0 (table v) (K4 v) ⟨1,(w! "1111011101111011110111"),(rep (w! "01100011001100") (n)) ++ ((w! "11"))⟩ = some ⟨2,(w! "01"),((w! "1100110001100011001100")) ++ (rep (w! "01100011001100") (n)) ++ ((w! "11"))⟩ := by cases v <;> rfl

def K5 (v : V) : Nat := match v with | .a => 14 | .b => 16 | .c => 14

theorem local5 (v : V) (L R : List Bool) : run0 (table v) (K5 v) ⟨2,((w! "0")) ++ (L),((w! "1100110001100011001100")) ++ ((w! "01100011001100")) ++ (R)⟩ = some ⟨2,((w! "0")) ++ ((w! "11110111011110")) ++ (L),((w! "1100110001100011001100")) ++ (R)⟩ := by cases v <;> rfl

theorem phase5 (v : V) (n : Nat) : run0 (table v) (K5 v*n) ⟨2,(w! "01"),((w! "1100110001100011001100")) ++ (rep (w! "01100011001100") (n)) ++ ((w! "11"))⟩ = some ⟨2,((w! "0")) ++ (rep (w! "11110111011110") (n)) ++ ((w! "1")),(w! "110011000110001100110011")⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR (table v) 2 (w! "0") (w! "1100110001100011001100") (w! "01100011001100") (w! "11110111011110") (K5 v) (local5 v) n (w! "1") (w! "11")

def K6 (v : V) : Nat := match v with | .a => 34 | .b => 40 | .c => 36

theorem phase6 (v : V) (n : Nat) : run0 (table v) (K6 v) ⟨2,((w! "0")) ++ (rep (w! "11110111011110") (n)) ++ ((w! "1")),(w! "110011000110001100110011")⟩ = some ⟨1,((w! "111011101111011110111011110")) ++ (rep (w! "11110111011110") (n)) ++ ((w! "1")),(w! "11")⟩ := by cases v <;> rfl

def K7 (v : V) : Nat := match v with | .a => 38 | .b => 38 | .c => 44

theorem local7 (v : V) (L R : List Bool) : run0 (table v) (K7 v) ⟨1,((w! "111011101111011110111011110")) ++ ((w! "11110111011110")) ++ (L),(R)⟩ = some ⟨1,((w! "111011101111011110111011110")) ++ (L),((w! "00110001100110")) ++ (R)⟩ := by cases v <;> rfl

theorem phase7 (v : V) (n : Nat) : run0 (table v) (K7 v*n) ⟨1,((w! "111011101111011110111011110")) ++ (rep (w! "11110111011110") (n)) ++ ((w! "1")),(w! "11")⟩ = some ⟨1,(w! "1110111011110111101110111101"),(rep (w! "00110001100110") (n)) ++ ((w! "11"))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL (table v) 1 (w! "111011101111011110111011110") [] (w! "11110111011110") (w! "00110001100110") (K7 v) (local7 v) n (w! "1") (w! "11")

def K8 (v : V) : Nat := match v with | .a => 99 | .b => 99 | .c => 117

theorem phase8 (v : V) (n : Nat) : run0 (table v) (K8 v) ⟨1,(w! "1110111011110111101110111101"),(rep (w! "00110001100110") (n)) ++ ((w! "11"))⟩ = some ⟨1,(w! "011"),((w! "011000110011000110001100110")) ++ (rep (w! "00110001100110") (n)) ++ ((w! "11"))⟩ := by cases v <;> rfl

def K9 (v : V) : Nat := match v with | .a => 14 | .b => 16 | .c => 14

theorem local9 (v : V) (L R : List Bool) : run0 (table v) (K9 v) ⟨1,((w! "0")) ++ (L),((w! "011000110011000110001100110")) ++ ((w! "00110001100110")) ++ (R)⟩ = some ⟨1,((w! "0")) ++ ((w! "11011110111101")) ++ (L),((w! "011000110011000110001100110")) ++ (R)⟩ := by cases v <;> rfl

theorem phase9 (v : V) (n : Nat) : run0 (table v) (K9 v*n) ⟨1,(w! "011"),((w! "011000110011000110001100110")) ++ (rep (w! "00110001100110") (n)) ++ ((w! "11"))⟩ = some ⟨1,((w! "0")) ++ (rep (w! "11011110111101") (n)) ++ ((w! "11")),(w! "01100011001100011000110011011")⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR (table v) 1 (w! "0") (w! "011000110011000110001100110") (w! "00110001100110") (w! "11011110111101") (K9 v) (local9 v) n (w! "11") (w! "11")

def K10 (v : V) : Nat := match v with | .a => 28 | .b => 32 | .c => 28

theorem phase10 (v : V) (n : Nat) : run0 (table v) (K10 v) ⟨1,((w! "0")) ++ (rep (w! "11011110111101") (n)) ++ ((w! "11")),(w! "01100011001100011000110011011")⟩ = some ⟨1,((w! "11101111011110111011110111101")) ++ (rep (w! "11011110111101") (n)) ++ ((w! "11")),(w! "1")⟩ := by cases v <;> rfl

def K11 (v : V) : Nat := match v with | .a => 38 | .b => 38 | .c => 44

theorem local11 (v : V) (L R : List Bool) : run0 (table v) (K11 v) ⟨1,((w! "11101111011110111011110111101")) ++ ((w! "11011110111101")) ++ (L),(R)⟩ = some ⟨1,((w! "11101111011110111011110111101")) ++ (L),((w! "01100011000110")) ++ (R)⟩ := by cases v <;> rfl

theorem phase11 (v : V) (n : Nat) : run0 (table v) (K11 v*n) ⟨1,((w! "11101111011110111011110111101")) ++ (rep (w! "11011110111101") (n)) ++ ((w! "11")),(w! "1")⟩ = some ⟨1,(w! "1110111101111011101111011110111"),(rep (w! "01100011000110") (n)) ++ ((w! "1"))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL (table v) 1 (w! "11101111011110111011110111101") [] (w! "11011110111101") (w! "01100011000110") (K11 v) (local11 v) n (w! "11") (w! "1")

def K12 (v : V) : Nat := match v with | .a => 89 | .b => 89 | .c => 103

theorem phase12 (v : V) (n : Nat) : run0 (table v) (K12 v) ⟨1,(w! "1110111101111011101111011110111"),(rep (w! "01100011000110") (n)) ++ ((w! "1"))⟩ = some ⟨2,(w! "01"),((w! "1100110001100011001100011000110")) ++ (rep (w! "01100011000110") (n)) ++ ((w! "1"))⟩ := by cases v <;> rfl

def K13 (v : V) : Nat := match v with | .a => 14 | .b => 16 | .c => 14

theorem local13 (v : V) (L R : List Bool) : run0 (table v) (K13 v) ⟨2,((w! "0")) ++ (L),((w! "1100110001100011001100011000110")) ++ ((w! "01100011000110")) ++ (R)⟩ = some ⟨2,((w! "0")) ++ ((w! "11110111011110")) ++ (L),((w! "1100110001100011001100011000110")) ++ (R)⟩ := by cases v <;> rfl

theorem phase13 (v : V) (n : Nat) : run0 (table v) (K13 v*n) ⟨2,(w! "01"),((w! "1100110001100011001100011000110")) ++ (rep (w! "01100011000110") (n)) ++ ((w! "1"))⟩ = some ⟨2,((w! "0")) ++ (rep (w! "11110111011110") (n)) ++ ((w! "1")),(w! "11001100011000110011000110001101")⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR (table v) 2 (w! "0") (w! "1100110001100011001100011000110") (w! "01100011000110") (w! "11110111011110") (K13 v) (local13 v) n (w! "1") (w! "1")

def K14 (v : V) : Nat := match v with | .a => 32 | .b => 36 | .c => 32

theorem phase14 (v : V) (n : Nat) : run0 (table v) (K14 v) ⟨2,((w! "0")) ++ (rep (w! "11110111011110") (n)) ++ ((w! "1")),(w! "11001100011000110011000110001101")⟩ = some ⟨1,((w! "111101111011101111011110111011110")) ++ (rep (w! "11110111011110") (n)) ++ ((w! "1")),[]⟩ := by cases v <;> rfl

def K15 (v : V) : Nat := match v with | .a => 38 | .b => 38 | .c => 44

theorem local15 (v : V) (L R : List Bool) : run0 (table v) (K15 v) ⟨1,((w! "111101111011101111011110111011110")) ++ ((w! "11110111011110")) ++ (L),(R)⟩ = some ⟨1,((w! "111101111011101111011110111011110")) ++ (L),((w! "01100110001100")) ++ (R)⟩ := by cases v <;> rfl

theorem phase15 (v : V) (n : Nat) : run0 (table v) (K15 v*n) ⟨1,((w! "111101111011101111011110111011110")) ++ (rep (w! "11110111011110") (n)) ++ ((w! "1")),[]⟩ = some ⟨1,(w! "1111011110111011110111101110111101"),(rep (w! "01100110001100") (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL (table v) 1 (w! "111101111011101111011110111011110") [] (w! "11110111011110") (w! "01100110001100") (K15 v) (local15 v) n (w! "1") []

def K16 (v : V) : Nat := match v with | .a => 90 | .b => 90 | .c => 104

theorem phase16 (v : V) (n : Nat) : run0 (table v) (K16 v) ⟨1,(w! "1111011110111011110111101110111101"),(rep (w! "01100110001100") (n))⟩ = some ⟨1,[],((w! "0011000110011000110001100110001100")) ++ (rep (w! "01100110001100") (n))⟩ := by cases v <;> rfl

theorem finalR (n : Nat) : (w! "0011000110011000110001100110001100") ++ rep (w! "01100110001100") n = (w! "001100011001100011") ++ rep (w! "00011001100011") n ++ (w! "0001100110001100") := by
  have h : (w! "00") ++ rep (w! "01100110001100") n = rep (w! "00011001100011") n ++ (w! "00") := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [rep]
      change ((w! "00011001100011") ++ (w! "00")) ++ rep (w! "01100110001100") n = (w! "00011001100011") ++ rep (w! "00011001100011") n ++ (w! "00")
      rw [List.append_assoc,ih,List.append_assoc]
  change ((w! "001100011001100011") ++ (w! "00011001100011") ++ (w! "00")) ++ rep (w! "01100110001100") n = (w! "001100011001100011") ++ rep (w! "00011001100011") n ++ ((w! "00011001100011") ++ (w! "00"))
  rw [List.append_assoc, h, List.append_assoc, ← List.append_assoc (w! "00011001100011"), ← rep_snoc]
  simp only [List.append_assoc]

def cost (v : V) (n : Nat) : Nat := match v with | .a => 486+208*n | .b => 502+216*n | .c => 552+232*n

theorem growth (v : V) (n : Nat) : run0 (table v) (cost v n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 v n) (phase1 v n)) (phase2 v n)) (phase3 v n)) (phase4 v n)) (phase5 v n)) (phase6 v n)) (phase7 v n)) (phase8 v n)) (phase9 v n)) (phase10 v n)) (phase11 v n)) (phase12 v n)) (phase13 v n)) (phase14 v n)) (phase15 v n)) (phase16 v n))
  rw [finalR n] at H
  have hc : K0 v+K1 v*n+K2 v+K3 v*n+K4 v+K5 v*n+K6 v+K7 v*n+K8 v+K9 v*n+K10 v+K11 v*n+K12 v+K13 v*n+K14 v+K15 v*n+K16 v = cost v n := by cases v <;> simp only [cost,K0,K1,K2,K3,K4,K5,K6,K7,K8,K9,K10,K11,K12,K13,K14,K15,K16] <;> omega
  rw [hc] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem positive (v : V) (n : Nat) : 0 < cost v n := by cases v <;> simp [cost] <;> omega
theorem never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) family (entryCost v) (cost v) (entry v) (positive v) (growth v) m hm

namespace M1603
abbrev table := _root_.BB6.Agent1Raw60LFPeriodic.table .a
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60LFPeriodic.never .a m hm
end M1603

namespace M1592
abbrev table := _root_.BB6.Agent1Raw60LFPeriodic.table .b
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60LFPeriodic.never .b m hm
end M1592

namespace M939
abbrev table := _root_.BB6.Agent1Raw60LFPeriodic.table .c
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60LFPeriodic.never .c m hm
end M939

#print axioms never

#print axioms growth

end BB6.Agent1Raw60LFPeriodic
