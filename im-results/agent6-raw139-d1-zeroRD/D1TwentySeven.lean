import Raw139Normalized
import SweepPumping
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent6D1TwentySeven
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent13BlankDelay
open BB6Coverage.Agent50Zipper
open Lean
macro "b!" s:str : term => do
  let xs ← s.getString.toList.mapM fun c => if c == '0' then `(false) else `(true)
  let xs := xs.toArray
  `([$xs,*])
def p : PartialMachine := FAR.fromCodes [7,16,11,9,14,1,2,13,20,24,8,15]
theorem pairRep (w : List Bool) (n : Nat) : rep (w++w) n = rep w (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1)=2*n+2 by omega]
    simp only [rep,ih,List.append_assoc]

theorem repAdd (w : List Bool) (m n : Nat) : rep w (m+n) = rep w m ++ rep w n := by
  induction m with
  | zero => simp [rep]
  | succ m ih => rw [show m+1+n = (m+n)+1 by omega, rep, ih, rep, List.append_assoc]

theorem rotate (a b : List Bool) (n : Nat) : a ++ rep (b++a) n = rep (a++b) n ++ a := by
  induction n with
  | zero => simp [rep]
  | succ n ih =>
    simp only [rep, List.append_assoc]
    rw [← List.append_assoc a b (a ++ rep (b++a) n), ih]
    simp only [List.append_assoc]

theorem rotTail (a b : List Bool) (n : Nat) (t : List Bool) :
  a ++ (rep (b++a) n ++ t) = rep (a++b) n ++ (a ++ t) := by
  simpa only [List.append_assoc] using congrArg (fun v => v ++ t) (rotate a b n)

theorem ordinary_raw (x y : Nat) (L : List Bool) :
    run0 p (124*x+24*y+519) ⟨2, b! "001010001000100100101001" ++ rep (b! "0010000100010") (x+1) ++ rep (b! "010") (y+2) ++ b! "000" ++ L, []⟩ = some ⟨2, b! "001010001000100100101001001000010" ++ rep (b! "0010001000010") (x+1) ++ b! "00" ++ rep (b! "100") (y+1) ++ b! "001001" ++ L, []⟩ := by
  have h1 : run0 p (89) ⟨2, b! "001010001000100100101001" ++ rep (b! "0010000100010") (x+1) ++ rep (b! "010") (y+2) ++ b! "000" ++ L, []⟩ = some ⟨3, b! "0100010" ++ rep (b! "0010000100010") (x+1) ++ rep (b! "010") (y+2) ++ b! "000" ++ L, b! "01101101101101011"⟩ := rfl
  have h2 : run0 p (21*(x+1)) ⟨3, b! "0100010" ++ rep (b! "0010000100010") (x+1) ++ rep (b! "010") (y+2) ++ b! "000" ++ L, b! "01101101101101011"⟩ = some ⟨3, b! "0100010" ++ rep (b! "010") (y+2) ++ b! "000" ++ L, rep (b! "1000110001101") (x+1) ++ b! "01101101101101011"⟩ := by
    have H := sweepL p 3 (b! "0100010") ([]) (b! "0010000100010") (b! "1000110001101") 21
      (by intro X Y; rfl) (x+1) (rep (b! "010") (y+2) ++ b! "000" ++ L) (b! "01101101101101011")
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append, rep] using H
  have h3 : run0 p (2) ⟨3, b! "0100010" ++ rep (b! "010") (y+2) ++ b! "000" ++ L, rep (b! "1000110001101") (x+1) ++ b! "01101101101101011"⟩ = some ⟨4, b! "00010" ++ rep (b! "010") (y+2) ++ b! "000" ++ L, b! "01" ++ rep (b! "1000110001101") (x+1) ++ b! "01101101101101011"⟩ := rfl
  have h4 : run0 p (11*(y+2)) ⟨4, b! "00010" ++ rep (b! "010") (y+2) ++ b! "000" ++ L, b! "01" ++ rep (b! "1000110001101") (x+1) ++ b! "01101101101101011"⟩ = some ⟨4, b! "00010000" ++ L, rep (b! "011") (y+2) ++ b! "01" ++ rep (b! "1000110001101") (x+1) ++ b! "01101101101101011"⟩ := by
    have H := sweepL p 4 (b! "00010") ([]) (b! "010") (b! "011") 11
      (by intro X Y; rfl) (y+2) (b! "000" ++ L) (b! "01" ++ rep (b! "1000110001101") (x+1) ++ b! "01101101101101011")
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append, rep] using H
  have h5 : run0 p (23) ⟨4, b! "00010000" ++ L, rep (b! "011") (y+2) ++ b! "01" ++ rep (b! "1000110001101") (x+1) ++ b! "01101101101101011"⟩ = some ⟨3, b! "1001001" ++ L, b! "1" ++ rep (b! "011") (y+2) ++ b! "01" ++ rep (b! "1000110001101") (x+1) ++ b! "01101101101101011"⟩ := rfl
  have h6 : run0 p (13*(y+2)) ⟨3, b! "1001001" ++ L, b! "1" ++ rep (b! "011") (y+2) ++ b! "01" ++ rep (b! "1000110001101") (x+1) ++ b! "01101101101101011"⟩ = some ⟨3, b! "1" ++ rep (b! "100") (y+2) ++ b! "001001" ++ L, b! "101" ++ rep (b! "1000110001101") (x+1) ++ b! "01101101101101011"⟩ := by
    have H := sweepR p 3 (b! "1") (b! "1") (b! "011") (b! "100") 13
      (by intro X Y; rfl) (y+2) (b! "001001" ++ L) (b! "01" ++ rep (b! "1000110001101") (x+1) ++ b! "01101101101101011")
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append, rep] using H
  have h7 : run0 p (103*(x+1)) ⟨3, b! "1" ++ rep (b! "100") (y+2) ++ b! "001001" ++ L, b! "101" ++ rep (b! "1000110001101") (x+1) ++ b! "01101101101101011"⟩ = some ⟨3, b! "11" ++ rep (b! "0010001000010") (x+1) ++ b! "00" ++ rep (b! "100") (y+1) ++ b! "001001" ++ L, b! "10101101101101101011"⟩ := by
    have H := sweepR p 3 (b! "11") (b! "101") (b! "1000110001101") (b! "0010001000010") 103
      (by intro X Y; rfl) (x+1) (b! "00" ++ rep (b! "100") (y+1) ++ b! "001001" ++ L) (b! "01101101101101011")
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append, rep] using H
  have h8 : run0 p (233) ⟨3, b! "11" ++ rep (b! "0010001000010") (x+1) ++ b! "00" ++ rep (b! "100") (y+1) ++ b! "001001" ++ L, b! "10101101101101101011"⟩ = some ⟨2, b! "001010001000100100101001001000010" ++ rep (b! "0010001000010") (x+1) ++ b! "00" ++ rep (b! "100") (y+1) ++ b! "001001" ++ L, []⟩ := rfl
  have H := join0 (join0 (join0 (join0 (join0 (join0 (join0 (h1) h2) h3) h4) h5) h6) h7) h8
  rw [show (89)+(21*(x+1))+(2)+(11*(y+2))+(23)+(13*(y+2))+(103*(x+1))+(233) = 124*x+24*y+519 by omega] at H
  exact H

theorem ordinary (x y : Nat) (L : List Bool) :
    run0 p (124*x+24*y+519) ⟨2, b! "001010001000100100101001" ++ rep (b! "0010000100010") (x+1) ++ rep (b! "010") (y+2) ++ b! "000" ++ L, []⟩ = some ⟨2, b! "001010001000100100101001" ++ rep (b! "0010000100010") (x+2) ++ rep (b! "010") (y) ++ b! "0001001" ++ L, []⟩ := by
  have H := ordinary_raw x y L
  have he : b! "001010001000100100101001001000010" ++ rep (b! "0010001000010") (x+1) ++ b! "00" ++ rep (b! "100") (y+1) ++ b! "001001" ++ L = b! "001010001000100100101001" ++ rep (b! "0010000100010") (x+2) ++ rep (b! "010") (y) ++ b! "0001001" ++ L := by
    calc
      b! "001010001000100100101001001000010" ++ rep (b! "0010001000010") (x+1) ++ b! "00" ++ rep (b! "100") (y+1) ++ b! "001001" ++ L = b! "001010001000100100101001" ++ b! "001000010" ++ rep (b! "0010001000010") (x+1) ++ b! "00" ++ rep (b! "100") (y+1) ++ b! "001001" ++ L := by simp only [rep, List.append_assoc, List.cons_append, List.nil_append]
      _ = b! "001010001000100100101001" ++ rep (b! "0010000100010") (x+1) ++ b! "001000010" ++ b! "00" ++ rep (b! "100") (y+1) ++ b! "001001" ++ L := by
        have h := rotTail (b! "001000010") (b! "0010") (x+1) (b! "00" ++ rep (b! "100") (y+1) ++ b! "001001" ++ L)
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using congrArg (fun v => b! "001010001000100100101001" ++ v) h
      _ = b! "001010001000100100101001" ++ rep (b! "0010000100010") (x+1) ++ b! "0010000100010" ++ b! "0" ++ rep (b! "100") (y) ++ b! "001001" ++ L := by simp only [rep, List.append_assoc, List.cons_append, List.nil_append]
      _ = b! "001010001000100100101001" ++ rep (b! "0010000100010") (x+1) ++ b! "0010000100010" ++ rep (b! "010") (y) ++ b! "0001001" ++ L := by
        have h := rotTail (b! "0") (b! "10") y (b! "001001" ++ L)
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using congrArg (fun v => b! "001010001000100100101001" ++ rep (b! "0010000100010") (x+1) ++ b! "0010000100010" ++ v) h
      _ = b! "001010001000100100101001" ++ rep (b! "0010000100010") (x+2) ++ rep (b! "010") (y) ++ b! "0001001" ++ L := by
        have hh : rep (b! "0010000100010") (x+2) = rep (b! "0010000100010") (x+1) ++ b! "0010000100010" := by
          have hh := repAdd (b! "0010000100010") (x+1) 1
          simpa only [rep, List.append_assoc, List.append_nil, List.cons_append, List.nil_append] using hh
        rw [hh]
        simp only [List.append_assoc]
  rw [he] at H
  exact H

theorem first_raw (x : Nat) (L : List Bool) :
    run0 p (21*x+141) ⟨2, b! "001010001000100100101001" ++ rep (b! "0010000100010") (x+1) ++ b! "00010011001" ++ L, []⟩ = some ⟨0, b! "1001000100110011001" ++ L, b! "000110001101" ++ rep (b! "1000110001101") (x) ++ b! "01101101101101011"⟩ := by
  have h1 : run0 p (89) ⟨2, b! "001010001000100100101001" ++ rep (b! "0010000100010") (x+1) ++ b! "00010011001" ++ L, []⟩ = some ⟨3, b! "0100010" ++ rep (b! "0010000100010") (x+1) ++ b! "00010011001" ++ L, b! "01101101101101011"⟩ := rfl
  have h2 : run0 p (21*(x+1)) ⟨3, b! "0100010" ++ rep (b! "0010000100010") (x+1) ++ b! "00010011001" ++ L, b! "01101101101101011"⟩ = some ⟨3, b! "010001000010011001" ++ L, rep (b! "1000110001101") (x+1) ++ b! "01101101101101011"⟩ := by
    have H := sweepL p 3 (b! "0100010") ([]) (b! "0010000100010") (b! "1000110001101") 21
      (by intro X Y; rfl) (x+1) (b! "00010011001" ++ L) (b! "01101101101101011")
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append, rep] using H
  have h3 : run0 p (31) ⟨3, b! "010001000010011001" ++ L, rep (b! "1000110001101") (x+1) ++ b! "01101101101101011"⟩ = some ⟨0, b! "1001000100110011001" ++ L, b! "000110001101" ++ rep (b! "1000110001101") (x) ++ b! "01101101101101011"⟩ := rfl
  have H := join0 (join0 (h1) h2) h3
  rw [show (89)+(21*(x+1))+(31) = 21*x+141 by omega] at H
  exact H

theorem first (x : Nat) (L : List Bool) :
    run0 p (21*x+141) ⟨2, b! "001010001000100100101001" ++ rep (b! "0010000100010") (x+1) ++ b! "00010011001" ++ L, []⟩ = some ⟨0, b! "1001000100110011001" ++ L, b! "000110001101" ++ rep (b! "1000110001101") (x) ++ b! "01101101101101011"⟩ := by
  exact first_raw x L

theorem init_raw (y : Nat) (L : List Bool) :
    run0 p (95) ⟨0, b! "1001000100110011001" ++ L, b! "000110001101" ++ rep (b! "1000110001101") (y+1) ++ b! "01101101101101011"⟩ = some ⟨0, b! "10010001001001001010000100011001" ++ L, b! "000110001101" ++ rep (b! "1000110001101") (y) ++ b! "01101101101101011"⟩ := by
  have h1 : run0 p (95) ⟨0, b! "1001000100110011001" ++ L, b! "000110001101" ++ rep (b! "1000110001101") (y+1) ++ b! "01101101101101011"⟩ = some ⟨0, b! "10010001001001001010000100011001" ++ L, b! "000110001101" ++ rep (b! "1000110001101") (y) ++ b! "01101101101101011"⟩ := rfl
  have H := h1
  rw [show (95) = 95 by omega] at H
  exact H

theorem init (y : Nat) (L : List Bool) :
    run0 p (95) ⟨0, b! "1001000100110011001" ++ L, b! "000110001101" ++ rep (b! "1000110001101") (y+1) ++ b! "01101101101101011"⟩ = some ⟨0, b! "10010001001001001010000100011001" ++ L, b! "000110001101" ++ rep (b! "1000110001101") (y) ++ b! "01101101101101011"⟩ := init_raw y L

theorem transfer_raw (x y : Nat) (L : List Bool) :
    run0 p (72*x+181) ⟨0, b! "1001000100100100101" ++ rep (b! "001") (3*x) ++ b! "00001" ++ rep (b! "0011") (x) ++ b! "0001" ++ L, b! "000110001101" ++ rep (b! "1000110001101") (y+1) ++ b! "01101101101101011"⟩ = some ⟨0, b! "100100010010010010" ++ rep (b! "100") (3*x+4) ++ b! "001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L, b! "000110001101" ++ rep (b! "1000110001101") (y) ++ b! "01101101101101011"⟩ := by
  have h1 : run0 p (64) ⟨0, b! "1001000100100100101" ++ rep (b! "001") (3*x) ++ b! "00001" ++ rep (b! "0011") (x) ++ b! "0001" ++ L, b! "000110001101" ++ rep (b! "1000110001101") (y+1) ++ b! "01101101101101011"⟩ = some ⟨3, b! "1001" ++ rep (b! "001") (3*x+1) ++ b! "00001" ++ rep (b! "0011") (x) ++ b! "0001" ++ L, b! "100011011010110110001101" ++ rep (b! "1000110001101") (y+1) ++ b! "01101101101101011"⟩ := rfl
  have h2 : run0 p (11*(3*x+1)) ⟨3, b! "1001" ++ rep (b! "001") (3*x+1) ++ b! "00001" ++ rep (b! "0011") (x) ++ b! "0001" ++ L, b! "100011011010110110001101" ++ rep (b! "1000110001101") (y+1) ++ b! "01101101101101011"⟩ = some ⟨3, b! "100100001" ++ rep (b! "0011") (x) ++ b! "0001" ++ L, b! "100" ++ rep (b! "011") (3*x+1) ++ b! "011011010110110001101" ++ rep (b! "1000110001101") (y+1) ++ b! "01101101101101011"⟩ := by
    have H := sweepL p 3 (b! "1001") (b! "100") (b! "001") (b! "011") 11
      (by intro X Y; rfl) (3*x+1) (b! "00001" ++ rep (b! "0011") (x) ++ b! "0001" ++ L) (b! "011011010110110001101" ++ rep (b! "1000110001101") (y+1) ++ b! "01101101101101011")
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append, rep] using H
  have h3 : run0 p (31) ⟨3, b! "100100001" ++ rep (b! "0011") (x) ++ b! "0001" ++ L, b! "100" ++ rep (b! "011") (3*x+1) ++ b! "011011010110110001101" ++ rep (b! "1000110001101") (y+1) ++ b! "01101101101101011"⟩ = some ⟨3, b! "1001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L, b! "1" ++ rep (b! "011") (3*x+2) ++ b! "011011010110110001101" ++ rep (b! "1000110001101") (y+1) ++ b! "01101101101101011"⟩ := rfl
  have h4 : run0 p (13*(3*x+2)) ⟨3, b! "1001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L, b! "1" ++ rep (b! "011") (3*x+2) ++ b! "011011010110110001101" ++ rep (b! "1000110001101") (y+1) ++ b! "01101101101101011"⟩ = some ⟨3, b! "1" ++ rep (b! "100") (3*x+2) ++ b! "001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L, b! "1011011010110110001101" ++ rep (b! "1000110001101") (y+1) ++ b! "01101101101101011"⟩ := by
    have H := sweepR p 3 (b! "1") (b! "1") (b! "011") (b! "100") 13
      (by intro X Y; rfl) (3*x+2) (b! "001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L) (b! "011011010110110001101" ++ rep (b! "1000110001101") (y+1) ++ b! "01101101101101011")
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append, rep] using H
  have h5 : run0 p (49) ⟨3, b! "1" ++ rep (b! "100") (3*x+2) ++ b! "001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L, b! "1011011010110110001101" ++ rep (b! "1000110001101") (y+1) ++ b! "01101101101101011"⟩ = some ⟨0, b! "100100010010010010" ++ rep (b! "100") (3*x+4) ++ b! "001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L, b! "000110001101" ++ rep (b! "1000110001101") (y) ++ b! "01101101101101011"⟩ := rfl
  have H := join0 (join0 (join0 (join0 (h1) h2) h3) h4) h5
  rw [show (64)+(11*(3*x+1))+(31)+(13*(3*x+2))+(49) = 72*x+181 by omega] at H
  exact H

theorem transfer (x y : Nat) (L : List Bool) :
    run0 p (72*x+181) ⟨0, b! "1001000100100100101" ++ rep (b! "001") (3*x) ++ b! "00001" ++ rep (b! "0011") (x) ++ b! "0001" ++ L, b! "000110001101" ++ rep (b! "1000110001101") (y+1) ++ b! "01101101101101011"⟩ = some ⟨0, b! "1001000100100100101" ++ rep (b! "001") (3*x+3) ++ b! "00001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L, b! "000110001101" ++ rep (b! "1000110001101") (y) ++ b! "01101101101101011"⟩ := by
  have H := transfer_raw x y L
  have he : b! "100100010010010010" ++ rep (b! "100") (3*x+4) ++ b! "001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L = b! "1001000100100100101" ++ rep (b! "001") (3*x+3) ++ b! "00001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L := by
    calc
      b! "100100010010010010" ++ rep (b! "100") (3*x+4) ++ b! "001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L = b! "100100010010010010" ++ rep (b! "100") (3*x+3) ++ b! "100001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L := by
        rw [show 3*x+4 = (3*x+3)+1 by omega, repAdd]
        simp only [rep, List.append_assoc, List.append_nil]
        rfl
      _ = b! "1001000100100100101" ++ rep (b! "001") (3*x+3) ++ b! "00001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L := by
        have h := rotTail (b! "1") (b! "00") (3*x+3) (b! "00001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L)
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using congrArg (fun v => b! "100100010010010010" ++ v) h.symm
  rw [he] at H
  exact H

theorem transferlast_raw (x : Nat) (L : List Bool) :
    run0 p (72*x+181) ⟨0, b! "1001000100100100101" ++ rep (b! "001") (3*x) ++ b! "00001" ++ rep (b! "0011") (x) ++ b! "0001" ++ L, b! "00011000110101101101101101011"⟩ = some ⟨0, b! "000100010010010010" ++ rep (b! "100") (3*x+4) ++ b! "001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L, b! "1101101101101011"⟩ := by
  have h1 : run0 p (64) ⟨0, b! "1001000100100100101" ++ rep (b! "001") (3*x) ++ b! "00001" ++ rep (b! "0011") (x) ++ b! "0001" ++ L, b! "00011000110101101101101101011"⟩ = some ⟨3, b! "1001" ++ rep (b! "001") (3*x+1) ++ b! "00001" ++ rep (b! "0011") (x) ++ b! "0001" ++ L, b! "10001101101011011000110101101101101101011"⟩ := rfl
  have h2 : run0 p (11*(3*x+1)) ⟨3, b! "1001" ++ rep (b! "001") (3*x+1) ++ b! "00001" ++ rep (b! "0011") (x) ++ b! "0001" ++ L, b! "10001101101011011000110101101101101101011"⟩ = some ⟨3, b! "100100001" ++ rep (b! "0011") (x) ++ b! "0001" ++ L, b! "100" ++ rep (b! "011") (3*x+1) ++ b! "01101101011011000110101101101101101011"⟩ := by
    have H := sweepL p 3 (b! "1001") (b! "100") (b! "001") (b! "011") 11
      (by intro X Y; rfl) (3*x+1) (b! "00001" ++ rep (b! "0011") (x) ++ b! "0001" ++ L) (b! "01101101011011000110101101101101101011")
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append, rep] using H
  have h3 : run0 p (31) ⟨3, b! "100100001" ++ rep (b! "0011") (x) ++ b! "0001" ++ L, b! "100" ++ rep (b! "011") (3*x+1) ++ b! "01101101011011000110101101101101101011"⟩ = some ⟨3, b! "1001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L, b! "1" ++ rep (b! "011") (3*x+2) ++ b! "01101101011011000110101101101101101011"⟩ := rfl
  have h4 : run0 p (13*(3*x+2)) ⟨3, b! "1001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L, b! "1" ++ rep (b! "011") (3*x+2) ++ b! "01101101011011000110101101101101101011"⟩ = some ⟨3, b! "1" ++ rep (b! "100") (3*x+2) ++ b! "001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L, b! "101101101011011000110101101101101101011"⟩ := by
    have H := sweepR p 3 (b! "1") (b! "1") (b! "011") (b! "100") 13
      (by intro X Y; rfl) (3*x+2) (b! "001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L) (b! "01101101011011000110101101101101101011")
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append, rep] using H
  have h5 : run0 p (49) ⟨3, b! "1" ++ rep (b! "100") (3*x+2) ++ b! "001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L, b! "101101101011011000110101101101101101011"⟩ = some ⟨0, b! "000100010010010010" ++ rep (b! "100") (3*x+4) ++ b! "001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L, b! "1101101101101011"⟩ := rfl
  have H := join0 (join0 (join0 (join0 (h1) h2) h3) h4) h5
  rw [show (64)+(11*(3*x+1))+(31)+(13*(3*x+2))+(49) = 72*x+181 by omega] at H
  exact H

theorem transferlast (x : Nat) (L : List Bool) :
    run0 p (72*x+181) ⟨0, b! "1001000100100100101" ++ rep (b! "001") (3*x) ++ b! "00001" ++ rep (b! "0011") (x) ++ b! "0001" ++ L, b! "00011000110101101101101101011"⟩ = some ⟨0, b! "0001000100100100101" ++ rep (b! "001") (3*x+3) ++ b! "00001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L, b! "1101101101101011"⟩ := by
  have H := transferlast_raw x L
  have he : b! "000100010010010010" ++ rep (b! "100") (3*x+4) ++ b! "001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L = b! "0001000100100100101" ++ rep (b! "001") (3*x+3) ++ b! "00001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L := by
    calc
      b! "000100010010010010" ++ rep (b! "100") (3*x+4) ++ b! "001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L = b! "000100010010010010" ++ rep (b! "100") (3*x+3) ++ b! "100001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L := by
        rw [show 3*x+4 = (3*x+3)+1 by omega, repAdd]
        simp only [rep, List.append_assoc, List.append_nil]
        rfl
      _ = b! "0001000100100100101" ++ rep (b! "001") (3*x+3) ++ b! "00001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L := by
        have h := rotTail (b! "1") (b! "00") (3*x+3) (b! "00001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L)
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using congrArg (fun v => b! "000100010010010010" ++ v) h.symm
  rw [he] at H
  exact H

theorem finish_raw (x : Nat) (L : List Bool) :
    run0 p (72*x+371) ⟨0, b! "0001000100100100101" ++ rep (b! "001") (3*x) ++ b! "00001" ++ rep (b! "0011") (x) ++ b! "0001" ++ L, b! "1101101101101011"⟩ = some ⟨2, b! "00101000100010010010" ++ rep (b! "100") (3*x+8) ++ b! "001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L, []⟩ := by
  have h1 : run0 p (170) ⟨0, b! "0001000100100100101" ++ rep (b! "001") (3*x) ++ b! "00001" ++ rep (b! "0011") (x) ++ b! "0001" ++ L, b! "1101101101101011"⟩ = some ⟨3, b! "1001" ++ rep (b! "001") (3*x+1) ++ b! "00001" ++ rep (b! "0011") (x) ++ b! "0001" ++ L, b! "10001101101101101101101011011011"⟩ := rfl
  have h2 : run0 p (11*(3*x+1)) ⟨3, b! "1001" ++ rep (b! "001") (3*x+1) ++ b! "00001" ++ rep (b! "0011") (x) ++ b! "0001" ++ L, b! "10001101101101101101101011011011"⟩ = some ⟨3, b! "100100001" ++ rep (b! "0011") (x) ++ b! "0001" ++ L, b! "100" ++ rep (b! "011") (3*x+1) ++ b! "01101101101101101101011011011"⟩ := by
    have H := sweepL p 3 (b! "1001") (b! "100") (b! "001") (b! "011") 11
      (by intro X Y; rfl) (3*x+1) (b! "00001" ++ rep (b! "0011") (x) ++ b! "0001" ++ L) (b! "01101101101101101101011011011")
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append, rep] using H
  have h3 : run0 p (31) ⟨3, b! "100100001" ++ rep (b! "0011") (x) ++ b! "0001" ++ L, b! "100" ++ rep (b! "011") (3*x+1) ++ b! "01101101101101101101011011011"⟩ = some ⟨3, b! "1001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L, b! "1" ++ rep (b! "011") (3*x+2) ++ b! "01101101101101101101011011011"⟩ := rfl
  have h4 : run0 p (13*(3*x+2)) ⟨3, b! "1001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L, b! "1" ++ rep (b! "011") (3*x+2) ++ b! "01101101101101101101011011011"⟩ = some ⟨3, b! "1" ++ rep (b! "100") (3*x+2) ++ b! "001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L, b! "101101101101101101101011011011"⟩ := by
    have H := sweepR p 3 (b! "1") (b! "1") (b! "011") (b! "100") 13
      (by intro X Y; rfl) (3*x+2) (b! "001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L) (b! "01101101101101101101011011011")
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append, rep] using H
  have h5 : run0 p (133) ⟨3, b! "1" ++ rep (b! "100") (3*x+2) ++ b! "001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L, b! "101101101101101101101011011011"⟩ = some ⟨2, b! "00101000100010010010" ++ rep (b! "100") (3*x+8) ++ b! "001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L, []⟩ := rfl
  have H := join0 (join0 (join0 (join0 (h1) h2) h3) h4) h5
  rw [show (170)+(11*(3*x+1))+(31)+(13*(3*x+2))+(133) = 72*x+371 by omega] at H
  exact H

theorem finish (x : Nat) (L : List Bool) :
    run0 p (72*x+371) ⟨0, b! "0001000100100100101" ++ rep (b! "001") (3*x) ++ b! "00001" ++ rep (b! "0011") (x) ++ b! "0001" ++ L, b! "1101101101101011"⟩ = some ⟨2, b! "001010001000100100101001" ++ rep (b! "001") (3*x+6) ++ b! "00001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L, []⟩ := by
  have H := finish_raw x L
  have he : b! "00101000100010010010" ++ rep (b! "100") (3*x+8) ++ b! "001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L = b! "001010001000100100101001" ++ rep (b! "001") (3*x+6) ++ b! "00001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L := by
    calc
      b! "00101000100010010010" ++ rep (b! "100") (3*x+8) ++ b! "001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L = b! "00101000100010010010100" ++ rep (b! "100") (3*x+6) ++ b! "100001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L := by
        rw [show 3*x+8 = 1+(3*x+6+1) by omega, repAdd]
        rw [show 3*x+6+1 = (3*x+6)+1 by omega, repAdd]
        simp only [rep, List.append_assoc, List.append_nil]
        rfl
      _ = b! "001010001000100100101001" ++ rep (b! "001") (3*x+6) ++ b! "00001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L := by
        have h := rotTail (b! "1") (b! "00") (3*x+6) (b! "00001" ++ rep (b! "0011") (x+1) ++ b! "0001" ++ L)
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using congrArg (fun v => b! "00101000100010010010100" ++ v) h.symm
  rw [he] at H
  exact H

theorem resetEven_raw (x : Nat) (L : List Bool) :
    run0 p (58*x+521) ⟨2, b! "001010001000100100101001" ++ rep (b! "001") (2*x+6) ++ b! "00001" ++ L, []⟩ = some ⟨2, b! "00101000100010010010100100100001000100" ++ rep (b! "100100") (x+2) ++ b! "00100101" ++ L, []⟩ := by
  have h1 : run0 p (91) ⟨2, b! "001010001000100100101001" ++ rep (b! "001") (2*x+6) ++ b! "00001" ++ L, []⟩ = some ⟨4, b! "00010" ++ rep (b! "001") (2*x+6) ++ b! "00001" ++ L, b! "0101101101101101011"⟩ := rfl
  have h2 : run0 p (32*(x+3)) ⟨4, b! "00010" ++ rep (b! "001") (2*x+6) ++ b! "00001" ++ L, b! "0101101101101101011"⟩ = some ⟨4, b! "0001000001" ++ L, rep (b! "011011") (x+3) ++ b! "0101101101101101011"⟩ := by
    have H := sweepL p 4 (b! "00010") ([]) (b! "001001") (b! "011011") 32
      (by intro X Y; rfl) (x+3) (b! "00001" ++ L) (b! "0101101101101101011")
    have hp : rep (b! "001001") (x+3) = rep (b! "001") (2*x+6) := by
      simpa only [List.cons_append, List.nil_append, show 2*(x+3) = 2*x+6 by omega] using pairRep (b! "001") (x+3)
    rw [hp] at H
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using H
  have h3 : run0 p (23) ⟨4, b! "0001000001" ++ L, rep (b! "011011") (x+3) ++ b! "0101101101101101011"⟩ = some ⟨3, b! "100100101" ++ L, b! "1" ++ rep (b! "011011") (x+3) ++ b! "0101101101101101011"⟩ := rfl
  have h4 : run0 p (26*(x+3)) ⟨3, b! "100100101" ++ L, b! "1" ++ rep (b! "011011") (x+3) ++ b! "0101101101101101011"⟩ = some ⟨3, b! "1" ++ rep (b! "100100") (x+3) ++ b! "00100101" ++ L, b! "10101101101101101011"⟩ := by
    have H := sweepR p 3 (b! "1") (b! "1") (b! "011011") (b! "100100") 26
      (by intro X Y; rfl) (x+3) (b! "00100101" ++ L) (b! "0101101101101101011")
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append, rep] using H
  have h5 : run0 p (233) ⟨3, b! "1" ++ rep (b! "100100") (x+3) ++ b! "00100101" ++ L, b! "10101101101101101011"⟩ = some ⟨2, b! "00101000100010010010100100100001000100" ++ rep (b! "100100") (x+2) ++ b! "00100101" ++ L, []⟩ := rfl
  have H := join0 (join0 (join0 (join0 (h1) h2) h3) h4) h5
  rw [show (91)+(32*(x+3))+(23)+(26*(x+3))+(233) = 58*x+521 by omega] at H
  exact H

theorem resetEven (x : Nat) (L : List Bool) :
    run0 p (58*x+521) ⟨2, b! "001010001000100100101001" ++ rep (b! "001") (2*x+6) ++ b! "00001" ++ L, []⟩ = some ⟨2, b! "0010100010001001001010010010000100010" ++ rep (b! "010") (2*x+4) ++ b! "000100101" ++ L, []⟩ := by
  have H := resetEven_raw x L
  have he : b! "00101000100010010010100100100001000100" ++ rep (b! "100100") (x+2) ++ b! "00100101" ++ L = b! "0010100010001001001010010010000100010" ++ rep (b! "010") (2*x+4) ++ b! "000100101" ++ L := by
    have hpair : rep (b! "100100") (x+2) = rep (b! "100") (2*x+4) := by
      simpa only [List.cons_append, List.nil_append, show 2*(x+2) = 2*x+4 by omega] using pairRep (b! "100") (x+2)
    rw [hpair]
    have h := rotTail (b! "0") (b! "10") (2*x+4) (b! "00100101" ++ L)
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using congrArg (fun v => b! "0010100010001001001010010010000100010" ++ v) h
  rw [he] at H
  exact H

theorem resetOdd1_raw (x : Nat) (L : List Bool) :
    run0 p (58*x+625) ⟨2, b! "001010001000100100101001" ++ rep (b! "001") (2*x+7) ++ b! "00001001100110011" ++ L, []⟩ = some ⟨2, b! "00101000100010010010100100100001000100" ++ rep (b! "100100") (x+3) ++ b! "01000001000110011" ++ L, []⟩ := by
  have h1 : run0 p (91) ⟨2, b! "001010001000100100101001" ++ rep (b! "001") (2*x+7) ++ b! "00001001100110011" ++ L, []⟩ = some ⟨4, b! "00010" ++ rep (b! "001") (2*x+7) ++ b! "00001001100110011" ++ L, b! "0101101101101101011"⟩ := rfl
  have h2 : run0 p (32*(x+3)) ⟨4, b! "00010" ++ rep (b! "001") (2*x+7) ++ b! "00001001100110011" ++ L, b! "0101101101101101011"⟩ = some ⟨4, b! "0001000100001001100110011" ++ L, rep (b! "011011") (x+3) ++ b! "0101101101101101011"⟩ := by
    have H := sweepL p 4 (b! "00010") ([]) (b! "001001") (b! "011011") 32
      (by intro X Y; rfl) (x+3) (b! "00100001001100110011" ++ L) (b! "0101101101101101011")
    have hp : rep (b! "001001") (x+3) = rep (b! "001") (2*x+6) := by
      simpa only [List.cons_append, List.nil_append, show 2*(x+3) = 2*x+6 by omega] using pairRep (b! "001") (x+3)
    rw [hp] at H
    have hs : rep (b! "001") (2*x+7) = rep (b! "001") (2*x+6) ++ b! "001" := by
      rw [show 2*x+7 = 2*x+6+1 by omega, repAdd]
      rfl
    rw [hs]
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using H
  have h3 : run0 p (101) ⟨4, b! "0001000100001001100110011" ++ L, rep (b! "011011") (x+3) ++ b! "0101101101101101011"⟩ = some ⟨3, b! "101000001000110011" ++ L, b! "1" ++ rep (b! "011011") (x+4) ++ b! "0101101101101101011"⟩ := rfl
  have h4 : run0 p (26*(x+4)) ⟨3, b! "101000001000110011" ++ L, b! "1" ++ rep (b! "011011") (x+4) ++ b! "0101101101101101011"⟩ = some ⟨3, b! "1" ++ rep (b! "100100") (x+4) ++ b! "01000001000110011" ++ L, b! "10101101101101101011"⟩ := by
    have H := sweepR p 3 (b! "1") (b! "1") (b! "011011") (b! "100100") 26
      (by intro X Y; rfl) (x+4) (b! "01000001000110011" ++ L) (b! "0101101101101101011")
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append, rep] using H
  have h5 : run0 p (233) ⟨3, b! "1" ++ rep (b! "100100") (x+4) ++ b! "01000001000110011" ++ L, b! "10101101101101101011"⟩ = some ⟨2, b! "00101000100010010010100100100001000100" ++ rep (b! "100100") (x+3) ++ b! "01000001000110011" ++ L, []⟩ := rfl
  have H := join0 (join0 (join0 (join0 (h1) h2) h3) h4) h5
  rw [show (91)+(32*(x+3))+(101)+(26*(x+4))+(233) = 58*x+625 by omega] at H
  exact H

theorem resetOdd1 (x : Nat) (L : List Bool) :
    run0 p (58*x+625) ⟨2, b! "001010001000100100101001" ++ rep (b! "001") (2*x+7) ++ b! "00001001100110011" ++ L, []⟩ = some ⟨2, b! "00101000100010010010100100100001000100" ++ rep (b! "100100") (x+3) ++ b! "01000001000110011" ++ L, []⟩ := by
  exact resetOdd1_raw x L

theorem resetOdd2_raw (x : Nat) (L : List Bool) :
    run0 p (76*x+893) ⟨2, b! "00101000100010010010100100100001000100" ++ rep (b! "100100") (x+3) ++ b! "01000001000110011" ++ L, []⟩ = some ⟨2, b! "00101000100010010010100100100001000100" ++ rep (b! "100100") (x+6) ++ b! "0010000101" ++ L, []⟩ := by
  have h1 : run0 p (109) ⟨2, b! "00101000100010010010100100100001000100" ++ rep (b! "100100") (x+3) ++ b! "01000001000110011" ++ L, []⟩ = some ⟨2, b! "001000100" ++ rep (b! "100100") (x+3) ++ b! "01000001000110011" ++ L, b! "00011000110101101101101101011"⟩ := rfl
  have h2 : run0 p (22*(x+3)) ⟨2, b! "001000100" ++ rep (b! "100100") (x+3) ++ b! "01000001000110011" ++ L, b! "00011000110101101101101101011"⟩ = some ⟨2, b! "00100010001000001000110011" ++ L, rep (b! "011011") (x+3) ++ b! "00011000110101101101101101011"⟩ := by
    have H := sweepL p 2 (b! "001000100") ([]) (b! "100100") (b! "011011") 22
      (by intro X Y; rfl) (x+3) (b! "01000001000110011" ++ L) (b! "00011000110101101101101101011")
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append, rep] using H
  have h3 : run0 p (103) ⟨2, b! "00100010001000001000110011" ++ L, rep (b! "011011") (x+3) ++ b! "00011000110101101101101101011"⟩ = some ⟨0, b! "001000101" ++ L, b! "11011" ++ rep (b! "011011") (x+5) ++ b! "00011000110101101101101101011"⟩ := rfl
  have h4 : run0 p (6*(x+5)) ⟨0, b! "001000101" ++ L, b! "11011" ++ rep (b! "011011") (x+5) ++ b! "00011000110101101101101101011"⟩ = some ⟨0, b! "0" ++ rep (b! "001001") (x+5) ++ b! "01000101" ++ L, b! "1101100011000110101101101101101011"⟩ := by
    have H := sweepR p 0 (b! "0") (b! "11011") (b! "011011") (b! "001001") 6
      (by intro X Y; rfl) (x+5) (b! "01000101" ++ L) (b! "00011000110101101101101101011")
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append, rep] using H
  have h5 : run0 p (11) ⟨0, b! "0" ++ rep (b! "001001") (x+5) ++ b! "01000101" ++ L, b! "1101100011000110101101101101101011"⟩ = some ⟨3, b! "1001" ++ rep (b! "001001") (x+6) ++ b! "01000101" ++ L, b! "1000110101101101101101011"⟩ := rfl
  have h6 : run0 p (22*(x+6)) ⟨3, b! "1001" ++ rep (b! "001001") (x+6) ++ b! "01000101" ++ L, b! "1000110101101101101101011"⟩ = some ⟨3, b! "100101000101" ++ L, b! "100" ++ rep (b! "011011") (x+6) ++ b! "0110101101101101101011"⟩ := by
    have H := sweepL p 3 (b! "1001") (b! "100") (b! "001001") (b! "011011") 22
      (by intro X Y; rfl) (x+6) (b! "01000101" ++ L) (b! "0110101101101101101011")
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append, rep] using H
  have h7 : run0 p (27) ⟨3, b! "100101000101" ++ L, b! "100" ++ rep (b! "011011") (x+6) ++ b! "0110101101101101101011"⟩ = some ⟨3, b! "10010000101" ++ L, b! "1011" ++ rep (b! "011011") (x+6) ++ b! "0110101101101101101011"⟩ := rfl
  have h8 : run0 p (26*(x+6)) ⟨3, b! "10010000101" ++ L, b! "1011" ++ rep (b! "011011") (x+6) ++ b! "0110101101101101101011"⟩ = some ⟨3, b! "1" ++ rep (b! "100100") (x+6) ++ b! "0010000101" ++ L, b! "10110110101101101101101011"⟩ := by
    have H := sweepR p 3 (b! "1") (b! "1011") (b! "011011") (b! "100100") 26
      (by intro X Y; rfl) (x+6) (b! "0010000101" ++ L) (b! "0110101101101101101011")
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append, rep] using H
  have h9 : run0 p (259) ⟨3, b! "1" ++ rep (b! "100100") (x+6) ++ b! "0010000101" ++ L, b! "10110110101101101101101011"⟩ = some ⟨2, b! "00101000100010010010100100100001000100" ++ rep (b! "100100") (x+6) ++ b! "0010000101" ++ L, []⟩ := rfl
  have H := join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (h1) h2) h3) h4) h5) h6) h7) h8) h9
  rw [show (109)+(22*(x+3))+(103)+(6*(x+5))+(11)+(22*(x+6))+(27)+(26*(x+6))+(259) = 76*x+893 by omega] at H
  exact H

theorem resetOdd2 (x : Nat) (L : List Bool) :
    run0 p (76*x+893) ⟨2, b! "00101000100010010010100100100001000100" ++ rep (b! "100100") (x+3) ++ b! "01000001000110011" ++ L, []⟩ = some ⟨2, b! "0010100010001001001010010010000100010" ++ rep (b! "010") (2*x+12) ++ b! "00010000101" ++ L, []⟩ := by
  have H := resetOdd2_raw x L
  have he : b! "00101000100010010010100100100001000100" ++ rep (b! "100100") (x+6) ++ b! "0010000101" ++ L = b! "0010100010001001001010010010000100010" ++ rep (b! "010") (2*x+12) ++ b! "00010000101" ++ L := by
    have hpair : rep (b! "100100") (x+6) = rep (b! "100") (2*x+12) := by
      simpa only [List.cons_append, List.nil_append, show 2*(x+6) = 2*x+12 by omega] using pairRep (b! "100") (x+6)
    rw [hpair]
    have h := rotTail (b! "0") (b! "10") (2*x+12) (b! "0010000101" ++ L)
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using congrArg (fun v => b! "0010100010001001001010010010000100010" ++ v) h
  rw [he] at H
  exact H


def Sec (x n : Nat) (L : List Bool) : Z0 :=
  ⟨2, b! "001010001000100100101001" ++ rep (b! "0010000100010") (x+1) ++
    rep (b! "010") (2*n) ++ b! "000" ++ L, []⟩

def Reach (a b : Z0) : Prop := ∃ t, run0 p t a = some b

theorem trans {a b c : Z0} (h : Reach a b) (g : Reach b c) : Reach a c := by
  obtain ⟨n,hn⟩ := h; obtain ⟨k,hk⟩ := g
  exact ⟨n+k,join0 hn hk⟩

theorem ordinarySec (x n : Nat) (L : List Bool) :
    Reach (Sec x (n+1) L) (Sec (x+1) n (b! "1001" ++ L)) := by
  refine ⟨124*x+24*(2*n)+519, ?_⟩
  simpa only [Sec, show 2*(n+1)=2*n+2 by omega, List.append_assoc, List.cons_append, List.nil_append] using ordinary x (2*n) L

theorem drain (x n : Nat) (L : List Bool) :
    Reach (Sec x n L) (Sec (x+n) 0 (rep (b! "1001") n ++ L)) := by
  induction n generalizing x L with
  | zero => exact ⟨0,rfl⟩
  | succ n ih =>
    have h := trans (ordinarySec x n L) (ih (x+1) (b! "1001" ++ L))
    have hr : rep (b! "1001") n ++ (b! "1001" ++ L) = rep (b! "1001") (n+1) ++ L := by
      rw [rep, ← List.append_assoc, rep_snoc, List.append_assoc]
    rw [hr, show x+1+n = x+(n+1) by omega] at h
    exact h

def Apos (x y : Nat) (L : List Bool) : Z0 :=
  ⟨0, b! "1001000100100100101" ++ rep (b! "001") (3*x) ++ b! "00001" ++ rep (b! "0011") x ++ b! "0001" ++ L,
    b! "000110001101" ++ rep (b! "1000110001101") y ++ b! "01101101101101011"⟩
def Azero (x : Nat) (L : List Bool) : Z0 :=
  ⟨0, b! "0001000100100100101" ++ rep (b! "001") (3*x) ++ b! "00001" ++ rep (b! "0011") x ++ b! "0001" ++ L,
    b! "1101101101101011"⟩

theorem transferSec (x y : Nat) (L : List Bool) : Reach (Apos x (y+1) L) (Apos (x+1) y L) :=
  ⟨72*x+181, by simpa only [Apos,show 3*(x+1)=3*x+3 by omega] using transfer x y L⟩

theorem transferLastSec (x : Nat) (L : List Bool) : Reach (Apos x 0 L) (Azero (x+1) L) :=
  ⟨72*x+181, by simpa only [Apos,Azero,rep,List.append_assoc,List.nil_append,List.cons_append,show 3*(x+1)=3*x+3 by omega] using transferlast x L⟩

theorem transferAll (x y : Nat) (L : List Bool) : Reach (Apos x y L) (Azero (x+y+1) L) := by
  induction y generalizing x with
  | zero => exact transferLastSec x L
  | succ y ih =>
    have h := trans (transferSec x y L) (ih (x+1))
    rw [show x+1+y+1=x+(y+1)+1 by omega] at h
    exact h

def Reset (n : Nat) (L : List Bool) : Z0 :=
  ⟨2, b! "001010001000100100101001" ++ rep (b! "001") n ++ b! "00001" ++ L, []⟩

def Good (z : Z0) : Prop := ∃ n L, z = Sec 0 (n+2) L

theorem resetGood (n : Nat) (L : List Bool) :
    ∃ t z, 0 < t ∧ Good z ∧ run0 p t (Reset (3*n+12) (rep (b! "0011") (n+3) ++ L)) = some z := by
  by_cases h : (3*n+12)%2=0
  · let x := (3*n+6)/2
    have hx : 3*n+12=2*x+6 := by dsimp [x]; omega
    let T := rep (b! "0011") (n+3) ++ L
    refine ⟨58*x+521, Sec 0 (x+2) (b! "100101" ++ T), by omega, ⟨x,_,rfl⟩, ?_⟩
    rw [hx]
    simpa only [Reset,Sec,rep, List.append_assoc,List.cons_append,List.nil_append,show 2*(x+2)=2*x+4 by omega,T] using resetEven x T
  · let x := (3*n+5)/2
    have hx : 3*n+12=2*x+7 := by dsimp [x]; omega
    let T := rep (b! "0011") n ++ L
    have hrun := join0 (resetOdd1 x T) (resetOdd2 x T)
    refine ⟨(58*x+625)+(76*x+893), Sec 0 ((x+4)+2) (b! "10000101" ++ T), by omega, ⟨x+4,_,rfl⟩, ?_⟩
    rw [hx]
    simpa only [Reset,Sec,rep,List.append_assoc,List.cons_append,List.nil_append,show 2*(x+4+2)=2*x+12 by omega,T] using hrun

theorem nextGood (a : Z0) (ha : Good a) : ∃ t z, 0 < t ∧ Good z ∧ run0 p t a = some z := by
  obtain ⟨n,L,rfl⟩ := ha
  let T := rep (b! "1001") n ++ L
  have h0 : Reach (Sec 0 (n+2) L) (Sec (n+2) 0 (b! "10011001" ++ T)) := by
    simpa only [Nat.zero_add,rep,T,List.append_assoc,List.cons_append,List.nil_append] using drain 0 (n+2) L
  let a1 : Z0 := ⟨0,b! "1001000100110011001" ++ T,b! "000110001101" ++ rep (b! "1000110001101") (n+2) ++ b! "01101101101101011"⟩
  have h1 : Reach (Sec (n+2) 0 (b! "10011001" ++ T)) a1 :=
    ⟨21*(n+2)+141, by simpa only [Sec,rep,List.append_assoc,List.cons_append,List.nil_append,a1] using first (n+2) T⟩
  have h2 : Reach a1 (Apos 0 (n+1) (b! "1001" ++ T)) :=
    ⟨95, by simpa only [a1,Apos,rep,Nat.mul_zero,List.append_assoc,List.cons_append,List.nil_append] using init (n+1) T⟩
  have h3 := transferAll 0 (n+1) (b! "1001" ++ T)
  have h3' : Reach (Apos 0 (n+1) (b! "1001" ++ T)) (Azero (n+2) (b! "1001" ++ T)) := by simpa only [Nat.zero_add] using h3
  let T2 := b! "00011001" ++ T
  have h4 : Reach (Azero (n+2) (b! "1001" ++ T)) (Reset (3*n+12) (rep (b! "0011") (n+3) ++ T2)) :=
    ⟨72*(n+2)+371, by simpa only [Azero,Reset,T2,List.append_assoc,List.cons_append,List.nil_append,show 3*(n+2)+6=3*n+12 by omega] using finish (n+2) (b! "1001" ++ T)⟩
  obtain ⟨t,ht⟩ := trans (trans (trans (trans h0 h1) h2) h3') h4
  obtain ⟨u,z,hpos,hgood,hr⟩ := resetGood n T2
  exact ⟨t+u,z,by omega,hgood,join0 ht hr⟩

-- The exact authentic blank-start seed.
def seed : Z0 := Sec 0 15 (b! "100001010011001100110011000000100011001")
theorem blank_seed : run0 p 13178 ⟨0,[],[]⟩ = some seed := by decide

theorem seedGood : Good seed := ⟨13,_,rfl⟩

theorem arbitrary : ∀ k, ∃ t z, k ≤ t ∧ Good z ∧ run0 p t ⟨0,[],[]⟩ = some z := by
  intro k
  induction k with
  | zero => exact ⟨13178,seed,by omega,seedGood,blank_seed⟩
  | succ k ih =>
    obtain ⟨t,z,ht,hg,hr⟩ := ih
    obtain ⟨u,v,hu,hv,hru⟩ := nextGood z hg
    exact ⟨t+u,v,by omega,hv,join0 hr hru⟩

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  intro n
  obtain ⟨t,v,ht,_,hr⟩ := arbitrary n
  have hz : (zrun p t start).map project = some v := (run_project p t start).trans hr
  cases h : zrun p t start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound p m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    change (run m n blank).bind (run m (t-n)) = some (embed z) at H
    cases he : run m n blank with
    | none =>
      rw [he] at H
      contradiction
    | some c => rfl

theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  .leaf p (fun m hm => weighted_never B m (never m hm))
#print axioms cover
#print axioms blank_seed
#print axioms nextGood
end BB6.Agent6D1TwentySeven
