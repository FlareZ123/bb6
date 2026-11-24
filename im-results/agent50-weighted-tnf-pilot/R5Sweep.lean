import SparseZipper

namespace BB6Coverage.Agent50R5Sweep
open BB6Coverage Agent50Zipper

def table (w : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,0⟩)
  | 1,false => some (some ⟨false,false,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨true,true,2⟩)
  | 2,true => some (some ⟨true,false,3⟩)
  | 3,false => some (some ⟨false,false,1⟩)
  | 3,true => some (some ⟨true,false,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨w,true,1⟩)
  | _,_ => none

def rep (P : List Bool) : Nat → List Bool
  | 0 => []
  | n+1 => P ++ rep P n

theorem rep_snoc (P : List Bool) (n : Nat) : rep P n ++ P = P ++ rep P n := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp only [rep,List.append_assoc,ih]

def P : List Bool := [false,true,true,true]
def Q : List Bool := [false,true,true,false]
def R : List Bool := [true,true,false,false]
def T : List Bool := [true,true,false]
def M : List Bool := [false,true,false]
def W : List Bool := [false,true,true,false,true]
def Y : List Bool := [true,true,false,true]

theorem turnWord (n : Nat) : T ++ rep Q n = rep R n ++ T := by
  induction n with
  | zero => simp [rep]
  | succ n ih =>
    rw [rep,rep,← List.append_assoc T Q,show T++Q=R++T by rfl,List.append_assoc,ih,List.append_assoc]

-- Leftwards B sweep over 0111, writes 0110.
theorem leftOne0 (L S : List Bool) :
    zrun (table true) 6 ⟨1,0,P++L,S⟩ = some ⟨1,-4,L,Q++S⟩ := by rfl

theorem leftOne (h : Int) (L S : List Bool) :
    zrun (table true) 6 ⟨1,h,P++L,S⟩ = some ⟨1,h-4,L,Q++S⟩ := by
  have hh := zrun_shift (table true) h 6 ⟨1,0,P++L,S⟩
  rw [leftOne0] at hh
  simpa [shift,show -4+h=h-4 by omega] using hh

theorem leftSweep (n : Nat) (h : Int) (L S : List Bool) :
    zrun (table true) (6*n) ⟨1,h,rep P n++L,S⟩ = some ⟨1,h-4*(n:Int),L,rep Q n++S⟩ := by
  induction n generalizing h S with
  | zero => simp [rep,zrun]
  | succ n ih =>
    have H := join (leftOne h (rep P n++L) S) (ih (h-4) (Q++S))
    rw [show 6*(n+1)=6+6*n by omega]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep Q n) Q S,rep_snoc Q n,
      Int.natCast_succ,show h-4-4*(n:Int)=h-4*((n:Int)+1) by omega] using H

theorem turn0 (S : List Bool) :
    zrun (table true) 17 ⟨1,0,M,Q++S⟩ = some ⟨1,1,W++[false],T++S⟩ := by rfl

theorem turn (h : Int) (S : List Bool) :
    zrun (table true) 17 ⟨1,h,M,Q++S⟩ = some ⟨1,h+1,W++[false],T++S⟩ := by
  have hh := zrun_shift (table true) h 17 ⟨1,0,M,Q++S⟩
  rw [turn0] at hh
  simpa [shift,Int.add_comm] using hh

theorem rightOne0 (L S : List Bool) :
    zrun (table true) 12 ⟨1,0,W++L,R++S⟩ = some ⟨1,4,W++Y++L,S⟩ := by rfl

theorem rightOne (h : Int) (L S : List Bool) :
    zrun (table true) 12 ⟨1,h,W++L,R++S⟩ = some ⟨1,h+4,W++Y++L,S⟩ := by
  have hh := zrun_shift (table true) h 12 ⟨1,0,W++L,R++S⟩
  rw [rightOne0] at hh
  simpa [shift,Int.add_comm] using hh

theorem rightSweep (n : Nat) (h : Int) (L S : List Bool) :
    zrun (table true) (12*n) ⟨1,h,W++L,rep R n++S⟩ = some ⟨1,h+4*(n:Int),W++rep Y n++L,S⟩ := by
  induction n generalizing h L with
  | zero => simp [rep,zrun]
  | succ n ih =>
    have H := join (rightOne h L (rep R n++S)) (ih (h+4) (Y++L))
    rw [show 12*(n+1)=12+12*n by omega]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep Y n) Y L,rep_snoc Y n,
      Int.natCast_succ,show h+4+4*(n:Int)=h+4*((n:Int)+1) by omega] using H

theorem finish0 (L : List Bool) :
    zrun (table true) 21 ⟨1,0,W++L,T⟩ = some ⟨1,5,P++P++[false,true]++L,[]⟩ := by rfl

theorem finish (h : Int) (L : List Bool) :
    zrun (table true) 21 ⟨1,h,W++L,T⟩ = some ⟨1,h+5,P++P++[false,true]++L,[]⟩ := by
  have hh := zrun_shift (table true) h 21 ⟨1,0,W++L,T⟩
  rw [finish0] at hh
  simpa [shift,Int.add_comm] using hh

theorem finishWord (n : Nat) : [false,true] ++ rep Y n ++ [false] = rep P n ++ M := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep,rep,← List.append_assoc [false,true] Y,show [false,true]++Y=P++[false,true] by rfl]
    simpa only [List.append_assoc] using congrArg (P++·) ih

def family (n : Nat) (h : Int) : Z := ⟨1,h,rep P (n+1)++M,[]⟩

theorem growth (n : Nat) (h : Int) :
    zrun (table true) (44+18*n) (family n h) = some (family (n+1) (h+2)) := by
  have h1 := leftSweep (n+1) h M []
  simp only [List.append_nil,rep] at h1
  have h2 := turn (h-4*((n+1:Nat):Int)) (rep Q n)
  rw [turnWord] at h2
  have h3 := rightSweep n (h-4*((n+1:Nat):Int)+1) [false] T
  have h4 := finish (h-4*((n+1:Nat):Int)+1+4*(n:Int)) (rep Y n++[false])
  have H := join (join (join h1 h2) h3) h4
  have hw : P++P++[false,true]++(rep Y n++[false]) = P++P++(rep P n++M) := by
    simpa only [List.append_assoc] using congrArg (fun x => P++P++x) (finishWord n)
  rw [hw] at H
  simpa only [family,rep,List.append_assoc,show 6*(n+1)+17+12*n+21=44+18*n by omega,
    show h-4*((n+1:Nat):Int)+1+4*(n:Int)+5=h+2 by omega] using H

def start : Z := ⟨0,0,[],[]⟩

theorem initial_embed : embed start = blank := by
  unfold embed start blank
  congr 1
  funext x
  simp [atCell]

theorem first : zrun (table true) 27 start = some (family 0 3) := by rfl

theorem arbitraryRun (n : Nat) : ∃ t h, n ≤ t ∧
    zrun (table true) t start = some (family n h) := by
  induction n with
  | zero => exact ⟨27,3,by omega,first⟩
  | succ n ih =>
    obtain ⟨t,h,ht,hr⟩ := ih
    exact ⟨t+(44+18*n),h+2,by omega,join hr (growth n h)⟩

theorem never_one (m : Machine) (hm : compatible (table true) m) : NeverHalts m := by
  intro n
  obtain ⟨t,h,ht,hr⟩ := arbitraryRun n
  have H := zrun_sound (table true) m hm t _ _ hr
  rw [initial_embed] at H
  rw [show t=n+(t-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some c => rfl

#print axioms never_one
end BB6Coverage.Agent50R5Sweep
