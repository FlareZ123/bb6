import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw391LEFTrio
open BB6Coverage BB6Coverage.Agent31Pump
open Lean in
macro "bits! " s:str : term => do
  let xs ← s.getString.toList.toArray.mapM fun c =>
    if c == '1' then `(true) else if c == '0' then `(false) else Macro.throwError "expected bit"
  `([$xs,*])

inductive V where
  | a | b | c

def startCost : V → Nat
  | .a => 43
  | .b => 49
  | .c => 45


def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,true,4⟩)
  | 5,true => some (some (match v with
      | .a => ⟨false,false,4⟩
      | .b => ⟨true,false,0⟩
      | .c => ⟨true,true,4⟩))
  | _,_ => none

def family (n : Nat) : Z0 := ⟨5,((bits! "10101000")) ++ (rep (bits! "11100") (n)) ++ ((bits! "1110011100111110011")),((bits! "0")) ++ (rep (bits! "110") (n)) ++ ((bits! "11"))⟩

theorem entry (v : V) : run0 (table v) 727 ⟨0,[],[]⟩ = some (family 0) := by cases v <;> rfl

theorem phase0 (v : V) (n : Nat) : run0 (table v) (startCost v) ⟨5,((bits! "10101000")) ++ (rep (bits! "11100") (n)) ++ ((bits! "1110011100111110011")),((bits! "0")) ++ (rep (bits! "110") (n)) ++ ((bits! "11"))⟩ = some ⟨4,((bits! "0")) ++ (rep (bits! "11100") (n)) ++ ((bits! "1110011100111110011")),((bits! "00110110")) ++ (rep (bits! "110") (n)) ++ ((bits! "11"))⟩ := by cases v <;> rfl

theorem local1 (v : V) (L R : List Bool) : run0 (table v) 15 ⟨4,((bits! "0")) ++ ((bits! "11100")) ++ (L),(R)⟩ = some ⟨4,((bits! "0")) ++ (L),((bits! "11000")) ++ (R)⟩ := by cases v <;> rfl

theorem phase1 (v : V) (n : Nat) : run0 (table v) (15*n) ⟨4,((bits! "0")) ++ (rep (bits! "11100") (n)) ++ ((bits! "1110011100111110011")),((bits! "00110110")) ++ (rep (bits! "110") (n)) ++ ((bits! "11"))⟩ = some ⟨4,((bits! "01110011100111110011")),(rep (bits! "11000") (n)) ++ ((bits! "00110110")) ++ (rep (bits! "110") (n)) ++ ((bits! "11"))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL (table v) 4 (bits! "0") [] (bits! "11100") (bits! "11000") 15 (local1 v) n (((bits! "1110011100111110011"))) (((bits! "00110110")) ++ (rep (bits! "110") (n)) ++ ((bits! "11")))

theorem phase2 (v : V) (n : Nat) : run0 (table v) 170 ⟨4,((bits! "01110011100111110011")),(rep (bits! "11000") (n)) ++ ((bits! "00110110")) ++ (rep (bits! "110") (n)) ++ ((bits! "11"))⟩ = some ⟨1,((bits! "01110011")),((bits! "0110001100011000")) ++ (rep (bits! "11000") (n)) ++ ((bits! "00110110")) ++ (rep (bits! "110") (n)) ++ ((bits! "11"))⟩ := by cases v <;> rfl

theorem local3 (v : V) (L R : List Bool) : run0 (table v) 9 ⟨1,((bits! "0")) ++ (L),((bits! "0110001100011000")) ++ ((bits! "11000")) ++ (R)⟩ = some ⟨1,((bits! "0")) ++ ((bits! "10011")) ++ (L),((bits! "0110001100011000")) ++ (R)⟩ := by cases v <;> rfl

theorem phase3 (v : V) (n : Nat) : run0 (table v) (9*n) ⟨1,((bits! "01110011")),((bits! "0110001100011000")) ++ (rep (bits! "11000") (n)) ++ ((bits! "00110110")) ++ (rep (bits! "110") (n)) ++ ((bits! "11"))⟩ = some ⟨1,((bits! "0")) ++ (rep (bits! "10011") (n)) ++ ((bits! "1110011")),((bits! "011000110001100000110110")) ++ (rep (bits! "110") (n)) ++ ((bits! "11"))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR (table v) 1 (bits! "0") (bits! "0110001100011000") (bits! "11000") (bits! "10011") 9 (local3 v) n (((bits! "1110011"))) (((bits! "00110110")) ++ (rep (bits! "110") (n)) ++ ((bits! "11")))

theorem phase4 (v : V) (n : Nat) : run0 (table v) 33 ⟨1,((bits! "0")) ++ (rep (bits! "10011") (n)) ++ ((bits! "1110011")),((bits! "011000110001100000110110")) ++ (rep (bits! "110") (n)) ++ ((bits! "11"))⟩ = some ⟨4,((bits! "0100111001110011")) ++ (rep (bits! "10011") (n)) ++ ((bits! "1110011")),((bits! "110110110")) ++ (rep (bits! "110") (n)) ++ ((bits! "11"))⟩ := by cases v <;> rfl

theorem local5 (v : V) (L R : List Bool) : run0 (table v) 15 ⟨4,((bits! "0100111001110011")) ++ ((bits! "10011")) ++ (L),(R)⟩ = some ⟨4,((bits! "0100111001110011")) ++ (L),((bits! "00110")) ++ (R)⟩ := by cases v <;> rfl

theorem phase5 (v : V) (n : Nat) : run0 (table v) (15*n) ⟨4,((bits! "0100111001110011")) ++ (rep (bits! "10011") (n)) ++ ((bits! "1110011")),((bits! "110110110")) ++ (rep (bits! "110") (n)) ++ ((bits! "11"))⟩ = some ⟨4,((bits! "01001110011100111110011")),(rep (bits! "00110") (n)) ++ ((bits! "110110110")) ++ (rep (bits! "110") (n)) ++ ((bits! "11"))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL (table v) 4 (bits! "0100111001110011") [] (bits! "10011") (bits! "00110") 15 (local5 v) n (((bits! "1110011"))) (((bits! "110110110")) ++ (rep (bits! "110") (n)) ++ ((bits! "11")))

theorem phase6 (v : V) (n : Nat) : run0 (table v) 179 ⟨4,((bits! "01001110011100111110011")),(rep (bits! "00110") (n)) ++ ((bits! "110110110")) ++ (rep (bits! "110") (n)) ++ ((bits! "11"))⟩ = some ⟨1,((bits! "01110011")),((bits! "0110001100011000110")) ++ (rep (bits! "00110") (n)) ++ ((bits! "110110110")) ++ (rep (bits! "110") (n)) ++ ((bits! "11"))⟩ := by cases v <;> rfl

theorem local7 (v : V) (L R : List Bool) : run0 (table v) 9 ⟨1,((bits! "0")) ++ (L),((bits! "0110001100011000110")) ++ ((bits! "00110")) ++ (R)⟩ = some ⟨1,((bits! "0")) ++ ((bits! "10011")) ++ (L),((bits! "0110001100011000110")) ++ (R)⟩ := by cases v <;> rfl

theorem phase7 (v : V) (n : Nat) : run0 (table v) (9*n) ⟨1,((bits! "01110011")),((bits! "0110001100011000110")) ++ (rep (bits! "00110") (n)) ++ ((bits! "110110110")) ++ (rep (bits! "110") (n)) ++ ((bits! "11"))⟩ = some ⟨1,((bits! "0")) ++ (rep (bits! "10011") (n)) ++ ((bits! "1110011")),((bits! "0110001100011000110110110110")) ++ (rep (bits! "110") (n)) ++ ((bits! "11"))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR (table v) 1 (bits! "0") (bits! "0110001100011000110") (bits! "00110") (bits! "10011") 9 (local7 v) n (((bits! "1110011"))) (((bits! "110110110")) ++ (rep (bits! "110") (n)) ++ ((bits! "11")))

theorem phase8 (v : V) (n : Nat) : run0 (table v) 42 ⟨1,((bits! "0")) ++ (rep (bits! "10011") (n)) ++ ((bits! "1110011")),((bits! "0110001100011000110110110110")) ++ (rep (bits! "110") (n)) ++ ((bits! "11"))⟩ = some ⟨5,((bits! "1010100011100111001110011")) ++ (rep (bits! "10011") (n)) ++ ((bits! "1110011")),((bits! "0110")) ++ (rep (bits! "110") (n)) ++ ((bits! "11"))⟩ := by cases v <;> rfl

theorem finalL (n : Nat) : ((bits! "1010100011100111001110011")) ++ (rep (bits! "10011") (n)) ++ ((bits! "1110011")) = ((bits! "1010100011100")) ++ (rep (bits! "11100") (n)) ++ ((bits! "1110011100111110011")) := by
  calc
    _ = ((bits! "101010001110011100111001")) ++ (rep (bits! "11001") (n)) ++ ((bits! "11110011")) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (((bits! "101010001110011100111001"))) (((bits! "1110011"))) (bits! "1001") true n
    _ = ((bits! "10101000111001110011100")) ++ (rep (bits! "11100") (n)) ++ ((bits! "111110011")) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (((bits! "10101000111001110011100"))) (((bits! "11110011"))) (bits! "1100") true n
    _ = ((bits! "1010100011100111001110")) ++ (rep (bits! "01110") (n)) ++ ((bits! "0111110011")) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (((bits! "1010100011100111001110"))) (((bits! "111110011"))) (bits! "1110") false n
    _ = ((bits! "101010001110011100111")) ++ (rep (bits! "00111") (n)) ++ ((bits! "00111110011")) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (((bits! "101010001110011100111"))) (((bits! "0111110011"))) (bits! "0111") false n
    _ = ((bits! "10101000111001110011")) ++ (rep (bits! "10011") (n)) ++ ((bits! "100111110011")) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (((bits! "10101000111001110011"))) (((bits! "00111110011"))) (bits! "0011") true n
    _ = ((bits! "1010100011100111001")) ++ (rep (bits! "11001") (n)) ++ ((bits! "1100111110011")) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (((bits! "1010100011100111001"))) (((bits! "100111110011"))) (bits! "1001") true n
    _ = ((bits! "101010001110011100")) ++ (rep (bits! "11100") (n)) ++ ((bits! "11100111110011")) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (((bits! "101010001110011100"))) (((bits! "1100111110011"))) (bits! "1100") true n
    _ = ((bits! "10101000111001110")) ++ (rep (bits! "01110") (n)) ++ ((bits! "011100111110011")) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (((bits! "10101000111001110"))) (((bits! "11100111110011"))) (bits! "1110") false n
    _ = ((bits! "1010100011100111")) ++ (rep (bits! "00111") (n)) ++ ((bits! "0011100111110011")) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (((bits! "1010100011100111"))) (((bits! "011100111110011"))) (bits! "0111") false n
    _ = ((bits! "101010001110011")) ++ (rep (bits! "10011") (n)) ++ ((bits! "10011100111110011")) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (((bits! "101010001110011"))) (((bits! "0011100111110011"))) (bits! "0011") true n
    _ = ((bits! "10101000111001")) ++ (rep (bits! "11001") (n)) ++ ((bits! "110011100111110011")) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (((bits! "10101000111001"))) (((bits! "10011100111110011"))) (bits! "1001") true n
    _ = ((bits! "1010100011100")) ++ (rep (bits! "11100") (n)) ++ ((bits! "1110011100111110011")) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (((bits! "1010100011100"))) (((bits! "110011100111110011"))) (bits! "1100") true n

theorem finalR (n : Nat) : ((bits! "0110")) ++ (rep (bits! "110") (n)) ++ ((bits! "11")) = ((bits! "0110")) ++ (rep (bits! "110") (n)) ++ ((bits! "11")) := by
  rfl

theorem growth (v : V) (n : Nat) : run0 (table v) (startCost v+424+48*n) (family n) = some (family (n+1)) := by
  have H := (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (phase0 v n) (phase1 v n)) (phase2 v n)) (phase3 v n)) (phase4 v n)) (phase5 v n)) (phase6 v n)) (phase7 v n)) (phase8 v n))
  rw [finalL n] at H
  rw [show startCost v+15*n+170+9*n+33+15*n+179+9*n+42=startCost v+424+48*n by omega] at H
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using H

theorem never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) family 727 (fun n => startCost v+424+48*n) (entry v) (by intro n; omega) (growth v) m hm

#print axioms never


end BB6.Agent11Raw391LEFTrio
