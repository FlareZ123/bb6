import Agent2BinaryPair

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace BB6.Agent2UnaryStack
open BB6Coverage BB6Coverage.Agent50Pump BB6Coverage.Agent50Zipper
open BB6.Agent2BinaryPair (rep_add)

/-- raw124/F1=1LA open leaf 235; F0 is unassigned. -/
def p : PartialMachine := fun s =>
  ([some (some ⟨true,true,1⟩),some (some ⟨false,false,4⟩),
    some (some ⟨true,true,2⟩),some (some ⟨true,true,1⟩),
    some (some ⟨false,true,3⟩),some (some ⟨false,false,0⟩),
    some (some ⟨true,false,3⟩),some (some ⟨true,true,4⟩),
    some (some ⟨false,true,2⟩),some (some ⟨true,false,5⟩),
    none,some (some ⟨true,false,0⟩)] : List (Option (Option Move)))[2*s.1.val+s.2.toNat]?.getD none

def Bz (l r : List Bool) : HZ := ⟨1,l,r⟩
def E (l r : List Bool) : HZ := ⟨4,l,r⟩
def B (k : Nat) (r : List Bool) : HZ := Bz (false :: List.replicate k true ++ [false]) r

def Reach (a c : HZ) : Prop := ∃ n, hrun p n a = some c
def Pos (a c : HZ) : Prop := ∃ n, 0<n ∧ hrun p n a = some c
theorem Reach.trans {a c d : HZ} : Reach a c → Reach c d → Reach a d := by
  rintro ⟨n,h⟩ ⟨m,g⟩; exact ⟨n+m,hjoin h g⟩
theorem Pos.trans {a c d : HZ} : Pos a c → Reach c d → Pos a d := by
  rintro ⟨n,hn,h⟩ ⟨m,g⟩; exact ⟨n+m,by omega,hjoin h g⟩
theorem Pos.reach {a c : HZ} : Pos a c → Reach a c := by
  rintro ⟨n,_,h⟩; exact ⟨n,h⟩

theorem framed {n : Nat} {a c : HZ} (hn : 0<n) (h : openRun p false false n a = some c) (L R : List Bool) :
    Pos (tail a L R) (tail c L R) := ⟨n,hn,openRun_sound _ _ _ _ _ _ L R (by simp) (by simp) h⟩

theorem aStart (L R : List Bool) : Pos (Bz (bits "0"++L) (bits "1"++R)) (E L (bits "00"++R)) := by
  have h : openRun p false false 3 (Bz (bits "0") (bits "1")) = some (E [] (bits "00")) := by decide
  exact framed (by decide) h L R

theorem bStart (L R : List Bool) : Pos (Bz (bits "01"++L) (bits "00"++R)) (E L (bits "0111"++R)) := by
  have h : openRun p false false 8 (Bz (bits "01") (bits "00")) = some (E [] (bits "0111")) := by decide
  exact framed (by decide) h L R

theorem bBlank (L : List Bool) : Pos (Bz (bits "01"++L) []) (E L (bits "0111")) := by
  have h : openRun p false true 8 (Bz (bits "01") []) = some (E [] (bits "0111")) := by decide
  exact ⟨8,by decide,by simpa only [tail,Bz,E,List.nil_append,List.append_nil] using openRun_sound p false true 8 _ _ L [] (by simp) (by simp) h⟩

theorem sweep (m : Nat) (L R : List Bool) : Reach (E (rep (bits "111") m++L) R) (E L (rep (bits "011") m++R)) := by
  have h : openRun p false false 3 (E (bits "111") []) = some (E [] (bits "011")) := by decide
  exact ⟨3*m,sweepL p 4 [] (bits "111") [] (bits "011") 3 h m L R⟩

theorem recover (R : List Bool) : Pos (E [false] (bits "0110"++R)) (B 3 R) := by
  have h : openRun p true false 8 (E [false] (bits "0110")) = some (B 3 []) := by decide
  exact ⟨8,by decide,by simpa only [tail,B,E,Bz,List.append_nil,List.nil_append] using openRun_sound p true false 8 _ _ [] R (by simp) (by simp) h⟩

theorem tripleRep (m : Nat) : rep (bits "111") m = List.replicate (3*m) true := by
  induction m with
  | zero => rfl
  | succ m ih => rw [rep,ih,show bits "111" = List.replicate 3 true by rfl,List.replicate_append_replicate]; congr 1; omega

theorem aReturn (m : Nat) (R : List Bool) : Pos (B (3*(m+1)) (bits "1"++R)) (B 3 (rep (bits "110") m++bits "0"++R)) := by
  have h := aStart (rep (bits "111") (m+1)++[false]) R
  have g := sweep (m+1) [false] (bits "00"++R)
  have j := recover (rep (bits "110") m++bits "0"++R)
  have hcomm := rep_intertwine (bits "0") (bits "011") (bits "110") rfl m
  have he : rep (bits "011") (m+1)++(bits "00"++R) = bits "0110"++(rep (bits "110") m++bits "0"++R) := by
    rw [rep]; simp only [List.append_assoc]
    change bits "011" ++ (rep (bits "011") m ++ (bits "0" ++ (bits "0"++R))) = _
    rw [← List.append_assoc (rep (bits "011") m) (bits "0"),hcomm]
    simp only [List.append_assoc]; rfl
  have hg := h.trans g
  rw [he] at hg
  have hh := hg.trans j.reach
  simp only [B,Bz,tripleRep,List.append_assoc] at hh ⊢
  exact hh

theorem bReturnCore (m : Nat) (R : List Bool) : Reach (E (rep (bits "111") (m+1)++[false]) (bits "0111"++R))
    (B 3 (rep (bits "110") m++bits "111"++R)) := by
  have h := sweep (m+1) [false] (bits "0111"++R)
  have j := recover (rep (bits "110") m++bits "111"++R)
  have hcomm := rep_intertwine (bits "0") (bits "011") (bits "110") rfl m
  have he : rep (bits "011") (m+1)++(bits "0111"++R) = bits "0110"++(rep (bits "110") m++bits "111"++R) := by
    rw [rep]; simp only [List.append_assoc]
    change bits "011" ++ (rep (bits "011") m ++ (bits "0" ++ (bits "111"++R))) = _
    rw [← List.append_assoc (rep (bits "011") m) (bits "0"),hcomm]
    simp only [List.append_assoc]; rfl
  rw [he] at h
  exact h.trans j.reach

theorem bReturn (m : Nat) (R : List Bool) : Pos (B (3*(m+1)+1) (bits "00"++R)) (B 3 (rep (bits "110") m++bits "111"++R)) := by
  have h := bStart (rep (bits "111") (m+1)++[false]) R
  have hh := h.trans (bReturnCore m R)
  simp only [B,Bz,tripleRep,List.replicate_succ,List.append_assoc] at hh ⊢
  exact hh

theorem bReturnBlank (m : Nat) : Pos (B (3*(m+1)+1) []) (B 3 (rep (bits "110") m++bits "111")) := by
  have h := bBlank (rep (bits "111") (m+1)++[false])
  have g := bReturnCore m []
  simp only [List.append_nil] at g
  have hh := h.trans g
  simp only [B,Bz,tripleRep,List.replicate_succ,List.append_assoc] at hh ⊢
  exact hh

theorem cTerm (k : Nat) : Pos (B (k+1) (bits "011")) (B (k+5) []) := by
  have h : openRun p false true 8 (Bz (bits "01") (bits "011")) = some (Bz (bits "011111") []) := by decide
  have H := openRun_sound p false true 8 _ _ (List.replicate k true++[false]) [] (by simp) (by simp) h
  refine ⟨8,by decide,?_⟩
  simp only [tail,B,Bz,List.append_nil,List.nil_append,List.replicate_succ,List.append_assoc,show k+5=k+1+1+1+1+1 by omega] at H ⊢
  exact H

theorem cFive (k : Nat) (R : List Bool) : Pos (B (k+1) (bits "01110"++R)) (B (k+6) R) := by
  have h : openRun p false false 9 (Bz (bits "01") (bits "01110")) = some (Bz (bits "0111111") []) := by decide
  have H := framed (by decide) h (List.replicate k true++[false]) R
  simp only [tail,B,Bz,List.append_nil,List.nil_append,List.replicate_succ,List.append_assoc,show k+6=k+1+1+1+1+1+1 by omega] at H ⊢
  exact H

theorem dReturn (k : Nat) (R : List Bool) : Pos (B (k+1) (bits "01011"++R)) (B (k+5) (bits "0"++R)) := by
  have h : openRun p false false 14 (Bz (bits "01") (bits "01011")) = some (Bz (bits "011111") (bits "0")) := by decide
  have H := framed (by decide) h (List.replicate k true++[false]) R
  simp only [tail,B,Bz,List.replicate_succ,List.append_assoc,show k+5=k+1+1+1+1+1 by omega] at H ⊢
  exact H

theorem eReturn (k : Nat) : Pos (B (k+1) (bits "01")) (B (k+7) []) := by
  have h : openRun p false true 16 (Bz (bits "01") (bits "01")) = some (Bz (bits "01111111") []) := by decide
  have H := openRun_sound p false true 16 _ _ (List.replicate k true++[false]) [] (by simp) (by simp) h
  refine ⟨16,by decide,?_⟩
  simp only [tail,B,Bz,List.append_nil,List.nil_append,List.replicate_succ,List.append_assoc,show k+7=k+1+1+1+1+1+1+1 by omega] at H ⊢
  exact H

#print axioms aReturn
#print axioms bReturn
#print axioms cTerm
#print axioms cFive
#print axioms dReturn
#print axioms eReturn

/-- Right stacks at length 3 modulo 9: blocks x1011y110, then x11 or x10111. -/
inductive R3 : List Bool → Prop where
  | terminal (x : Bool) : R3 [x,true,true]
  | short (x : Bool) : R3 [x,true,false,true,true,true]
  | block (x y : Bool) {r : List Bool} (h : R3 r) : R3 ([x,true,false,true,true,y,true,true,false] ++ r)

/-- Right stacks at length 7 modulo 9: empty, 01, or 0y110 followed by R3. -/
inductive R7 : List Bool → Prop where
  | empty : R7 []
  | short : R7 [false,true]
  | block (y : Bool) {r : List Bool} (h : R3 r) : R7 ([false,y,true,true,false] ++ r)

theorem R3.prepend (n : Nat) {r : List Bool} (h : R3 r) : R3 (rep (bits "110") (3*n) ++ r) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [show 3*(n+1)=3+3*n by omega,rep_add,List.append_assoc]
    exact R3.block true false ih

inductive Inv : HZ → Prop where
  | three (n : Nat) {r : List Bool} (h : R3 r) : Inv (B (3+9*n) r)
  | four (n : Nat) : Inv (B (4+9*n) [])
  | seven (n : Nat) {r : List Bool} (h : R7 r) : Inv (B (7+9*n) r)

theorem a9 (n : Nat) (r : List Bool) : Pos (B (3+9*n) (true::r)) (B 3 (rep (bits "110") (3*n) ++ false::r)) := by
  have h := aReturn (3*n) r
  rw [show 3+9*n=3*(3*n+1) by omega]
  simp only [List.append_assoc] at h
  exact h

theorem four9 (n : Nat) : Pos (B (4+9*n) []) (B 3 (rep (bits "110") (3*n) ++ bits "111")) := by
  rw [show 4+9*n=3*(3*n+1)+1 by omega]
  exact bReturnBlank (3*n)

theorem sevenBlank (n : Nat) : Pos (B (7+9*n) []) (B 3 (rep (bits "110") (3*n) ++ bits "110111")) := by
  have h := bReturnBlank (3*n+1)
  rw [show 7+9*n=3*(3*n+1+1)+1 by omega]
  rw [rep_add,List.append_assoc] at h
  exact h

theorem seven00 (n : Nat) (r : List Bool) : Pos (B (7+9*n) (bits "00110"++r)) (B 3 (rep (bits "110") (3*n) ++ bits "110111110" ++ r)) := by
  have h := bReturn (3*n+1) (bits "110"++r)
  rw [show 7+9*n=3*(3*n+1+1)+1 by omega]
  rw [rep_add] at h
  simp only [List.append_assoc] at h ⊢
  exact h

theorem c9 (n : Nat) : Pos (B (3+9*n) (bits "011")) (B (7+9*n) []) := by
  have h := cTerm (2+9*n)
  rw [show 2+9*n+1=3+9*n by omega, show 2+9*n+5=7+9*n by omega] at h
  exact h

theorem d9 (n : Nat) (r : List Bool) : Pos (B (3+9*n) (bits "01011"++r)) (B (7+9*n) (bits "0"++r)) := by
  have h := dReturn (2+9*n) r
  rw [show 2+9*n+1=3+9*n by omega,show 2+9*n+5=7+9*n by omega] at h
  exact h

theorem c7 (n : Nat) (r : List Bool) : Pos (B (7+9*n) (bits "01110"++r)) (B (3+9*(n+1)) r) := by
  have h := cFive (6+9*n) r
  rw [show 6+9*n+1=7+9*n by omega,show 6+9*n+6=3+9*(n+1) by omega] at h
  exact h

theorem e7 (n : Nat) : Pos (B (7+9*n) (bits "01")) (B (4+9*(n+1)) []) := by
  have h := eReturn (6+9*n)
  rw [show 6+9*n+1=7+9*n by omega,show 6+9*n+7=4+9*(n+1) by omega] at h
  exact h

theorem inv_next {c : HZ} (hc : Inv c) : ∃ d, Pos c d ∧ Inv d := by
  cases hc with
  | four n =>
    exact ⟨_,four9 n,Inv.three 0 (R3.prepend n (R3.terminal true))⟩
  | three n hr =>
    cases hr with
    | terminal x =>
      cases x with
      | false => exact ⟨_,c9 n,Inv.seven n R7.empty⟩
      | true => exact ⟨_,a9 n [true,true],Inv.three 0 (R3.prepend n (R3.terminal false))⟩
    | short x =>
      cases x with
      | false => exact ⟨_,d9 n [true],Inv.seven n R7.short⟩
      | true => exact ⟨_,a9 n [true,false,true,true,true],Inv.three 0 (R3.prepend n (R3.short false))⟩
    | @block x y r h =>
      cases x with
      | false => exact ⟨_,d9 n ([y,true,true,false]++r),Inv.seven n (R7.block y h)⟩
      | true => exact ⟨_,a9 n ([true,false,true,true,y,true,true,false]++r),Inv.three 0 (R3.prepend n (R3.block false y h))⟩
  | seven n hr =>
    cases hr with
    | empty => exact ⟨_,sevenBlank n,Inv.three 0 (R3.prepend n (R3.short true))⟩
    | short => exact ⟨_,e7 n,Inv.four (n+1)⟩
    | @block y r h =>
      cases y with
      | false =>
        have hh := seven00 n r
        simp only [List.append_assoc] at hh
        exact ⟨_,hh,Inv.three 0 (R3.prepend n (R3.block true true h))⟩
      | true => exact ⟨_,c7 n r,Inv.three (n+1) h⟩

theorem entry : hrun p 18 ⟨0,[],[]⟩ = some (B 4 []) := by decide

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  have H : ∀ k : Nat, ∃ n c, k≤n ∧ hrun p n ⟨0,[],[]⟩ = some c ∧ Inv c := by
    intro k
    induction k with
    | zero => exact ⟨18,B 4 [],by decide,entry,Inv.four 0⟩
    | succ k ih =>
      obtain ⟨n,c,hn,hc,hi⟩ := ih
      obtain ⟨d,⟨t,ht,hd⟩,hid⟩ := inv_next hi
      exact ⟨n+t,d,by omega,hjoin hc hd,hid⟩
  intro n
  obtain ⟨k,c,hk,hc,_⟩ := H n
  obtain ⟨h',hz⟩ := hrun_sound p k _ _ 0 hc
  have Hraw := zrun_sound p m hm k _ _ hz
  rw [blank_embed,show k=n+(k-n) by omega,run_append] at Hraw
  cases hr : run m n blank with
  | none => simp [hr] at Hraw
  | some z => rfl

#print axioms inv_next
#print axioms never
end BB6.Agent2UnaryStack
