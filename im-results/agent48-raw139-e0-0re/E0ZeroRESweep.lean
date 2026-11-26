import SparseZipper
import FastThreeHoleAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent48E0ZeroRESweep
open BB6Coverage Agent50Zipper

/-- The exact exceptional partial table. B/1 is never queried. -/
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨true,false,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,true,0⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨false,true,4⟩)
  | 4,true => some (some ⟨true,true,2⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def ones (n : Nat) : List Bool := List.replicate n true
def zeros (n : Nat) : List Bool := List.replicate n false

theorem ones_add (n m : Nat) : ones (n+m) = ones n ++ ones m := by
  exact List.replicate_append_replicate.symm

def X (n k : Nat) (h : Int) : Z :=
  ⟨0,h,[false,true,true],zeros 4 ++ ones (4*n) ++ zeros k⟩

theorem prep0 (R : List Bool) :
    zrun table 26 ⟨0,0,[false,true,true],zeros 4 ++ R⟩ =
      some ⟨3,4,false::(ones 6++[false]),R⟩ := by rfl

theorem pair0 (L R : List Bool) :
    zrun table 4 ⟨3,0,false::L,true::true::R⟩ =
      some ⟨3,2,false::true::true::L,R⟩ := by rfl

theorem turn0 (L : List Bool) (k : Nat) :
    zrun table 5 ⟨3,0,false::L,zeros k⟩ =
      some ⟨4,1,true::true::L,false::true::zeros (k-3)⟩ := by
  cases k with
  | zero => rfl
  | succ k => cases k with
    | zero => rfl
    | succ k => cases k with
      | zero => rfl
      | succ k => rfl

theorem left0 (L R : List Bool) :
    zrun table 3 ⟨4,0,true::L,false::R⟩ =
      some ⟨4,-1,L,false::true::R⟩ := by rfl

theorem finish0 (R : List Bool) :
    zrun table 20 ⟨4,0,[false],false::(ones 5++R)⟩ =
      some ⟨0,2,[false,true,true],zeros 4++R⟩ := by rfl

theorem prep (h : Int) (R : List Bool) :
    zrun table 26 ⟨0,h,[false,true,true],zeros 4 ++ R⟩ =
      some ⟨3,h+4,false::(ones 6++[false]),R⟩ := by
  have H := zrun_shift table h 26 ⟨0,0,[false,true,true],zeros 4 ++ R⟩
  rw [prep0] at H
  simpa [shift,Int.add_comm] using H

theorem pair (h : Int) (L R : List Bool) :
    zrun table 4 ⟨3,h,false::L,true::true::R⟩ =
      some ⟨3,h+2,false::true::true::L,R⟩ := by
  have H := zrun_shift table h 4 ⟨3,0,false::L,true::true::R⟩
  rw [pair0] at H
  simpa [shift,Int.add_comm] using H

theorem turn (h : Int) (L : List Bool) (k : Nat) :
    zrun table 5 ⟨3,h,false::L,zeros k⟩ =
      some ⟨4,h+1,true::true::L,false::true::zeros (k-3)⟩ := by
  have H := zrun_shift table h 5 ⟨3,0,false::L,zeros k⟩
  rw [turn0] at H
  simpa [shift,Int.add_comm] using H

theorem left (h : Int) (L R : List Bool) :
    zrun table 3 ⟨4,h,true::L,false::R⟩ =
      some ⟨4,h-1,L,false::true::R⟩ := by
  have H := zrun_shift table h 3 ⟨4,0,true::L,false::R⟩
  rw [left0] at H
  simpa [shift,show -1+h=h-1 by omega] using H

theorem finish (h : Int) (R : List Bool) :
    zrun table 20 ⟨4,h,[false],false::(ones 5++R)⟩ =
      some ⟨0,h+2,[false,true,true],zeros 4++R⟩ := by
  have H := zrun_shift table h 20 ⟨4,0,[false],false::(ones 5++R)⟩
  rw [finish0] at H
  simpa [shift,Int.add_comm] using H

theorem rightSweep (n : Nat) (h : Int) (L R : List Bool) :
    zrun table (4*n) ⟨3,h,false::L,ones (2*n)++R⟩ =
      some ⟨3,h+2*(n:Int),false::(ones (2*n)++L),R⟩ := by
  induction n generalizing h L with
  | zero => simp [ones,zrun]
  | succ n ih =>
    have H := join (pair h L (ones (2*n)++R)) (ih (h+2) (true::true::L))
    rw [show 4*(n+1)=4+4*n by omega]
    have hi : ones (2*(n+1))++R = true::true::(ones (2*n)++R) := by
      rw [show 2*(n+1)=2+2*n by omega,ones_add,List.append_assoc];rfl
    have hl : ones (2*n)++true::true::L = ones (2*(n+1))++L := by
      rw [show 2*(n+1)=2*n+2 by omega,ones_add,List.append_assoc];rfl
    simpa only [hi,hl,Int.natCast_succ,show h+2+2*(n:Int)=h+2*((n:Int)+1) by omega] using H

theorem leftSweep (n : Nat) (h : Int) (L R : List Bool) :
    zrun table (3*n) ⟨4,h,ones n++L,false::R⟩ =
      some ⟨4,h-(n:Int),L,false::(ones n++R)⟩ := by
  induction n generalizing h R with
  | zero => simp [ones,zrun]
  | succ n ih =>
    have H := join (left h (ones n++L) R) (ih (h-1) (true::R))
    rw [show 3*(n+1)=3+3*n by omega]
    have hi : ones (n+1)++L = true::(ones n++L) := by
      rw [show n+1=1+n by omega,ones_add,List.append_assoc];rfl
    have hr : ones n++true::R = ones (n+1)++R := by
      rw [ones_add,List.append_assoc];rfl
    simpa only [hi,hr,Int.natCast_succ,show h-1-(n:Int)=h-((n:Int)+1) by omega] using H

theorem growth (n k : Nat) (h : Int) :
    zrun table (20*n+75) (X n k h) = some (X (n+1) (k-3) (h-1)) := by
  have h1 := prep h (ones (4*n)++zeros k)
  have h2 := rightSweep (2*n) (h+4) (ones 6++[false]) (zeros k)
  have h2' : zrun table (8*n) ⟨3,h+4,false::(ones 6++[false]),ones (4*n)++zeros k⟩ =
      some ⟨3,h+4+4*(n:Int),false::(ones (4*n+6)++[false]),zeros k⟩ := by
    simpa only [show 4*(2*n)=8*n by omega,show 2*(2*n)=4*n by omega,
      show 2*((2*n:Nat):Int)=4*(n:Int) by omega,
      ones_add,List.append_assoc] using h2
  have h3 := turn (h+4+4*(n:Int)) (ones (4*n+6)++[false]) k
  have h4 := leftSweep (4*n+8) (h+4+4*(n:Int)+1) [false] (true::zeros (k-3))
  have hl : true::true::(ones (4*n+6)++[false]) = ones (4*n+8)++[false] := by
    rw [show 4*n+8=2+(4*n+6) by omega,ones_add 2 (4*n+6),List.append_assoc];rfl
  have hr : ones (4*n+8)++true::zeros (k-3) = ones 5++(ones (4*(n+1))++zeros (k-3)) := by
    have he : ones (4*n+8)++true::zeros (k-3) = ones (4*n+9)++zeros (k-3) := by
      rw [show 4*n+9=(4*n+8)+1 by omega,ones_add (4*n+8) 1,List.append_assoc];rfl
    rw [he,show 4*n+9=5+4*(n+1) by omega,ones_add 5 (4*(n+1)),List.append_assoc]
  have hh : h+4+4*(n:Int)+1-((4*n+8:Nat):Int)=h-3 := by omega
  have h4' : zrun table (3*(4*n+8)) ⟨4,h+4+4*(n:Int)+1,true::true::(ones (4*n+6)++[false]),false::true::zeros (k-3)⟩ =
      some ⟨4,h-3,[false],false::(ones 5++(ones (4*(n+1))++zeros (k-3)))⟩ := by
    rw [hl];simpa only [hr,hh] using h4
  have h5 := finish (h-3) (ones (4*(n+1))++zeros (k-3))
  have H := join (join (join (join h1 h2') h3) h4') h5
  simpa only [X,List.append_assoc,show 26+8*n+5+3*(4*n+8)+20=20*n+75 by omega,
    show h-3+2=h-1 by omega] using H

def start : Z := ⟨0,0,[],[]⟩
theorem first : zrun table 636 start = some (X 0 17 (-4)) := by rfl

theorem arbitraryRun (n : Nat) : ∃ t a k h, n ≤ t ∧ zrun table t start = some (X a k h) := by
  induction n with
  | zero => exact ⟨636,0,17,-4,by omega,first⟩
  | succ n ih =>
    obtain ⟨t,a,k,h,ht,hr⟩ := ih
    exact ⟨t+(20*a+75),a+1,k-3,h-1,by omega,join hr (growth a k h)⟩

theorem start_embed : embed start = blank := by
  unfold embed start blank
  congr 1
  funext x
  simp [atCell]

theorem table_never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,a,k,h,ht,hr⟩ := arbitraryRun n
  have H := zrun_sound table m hm t _ _ hr
  rw [start_embed] at H
  rw [show t=n+(t-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some c => rfl

def ctr : PartialMachine := FAR.fromCodes [7,21,11,24,14,23,3,16,17,11,15,20]
theorem same : ctr = table :=
  BB6.Agent31ThreeHole.tableOK_sound _ _ (by decide +kernel)
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  table_never m (by simpa only [← same] using hm)

#print axioms growth
#print axioms first
#print axioms arbitraryRun
#print axioms never
end BB6Coverage.Agent48E0ZeroRESweep
