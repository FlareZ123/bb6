import SparseZipper
import FastThreeHoleAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent14E0LFResidual10338
open BB6Coverage Agent50Zipper

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨true,false,3⟩)
  | 3,false => some (some ⟨true,true,0⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,true,2⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def ones (n : Nat) : List Bool := List.replicate n true
def zeros (n : Nat) : List Bool := List.replicate n false

theorem ones_add (n m : Nat) : ones (n+m) = ones n ++ ones m :=
  List.replicate_append_replicate.symm

def atR (q : Fin 6) (h : Int) (L R : List Bool) : Z :=
  ⟨q,h,R.headD false::L,R.tail⟩

def X (k : Nat) (h : Int) : Z :=
  ⟨5,h,[],zeros 2 ++ ones (2*k+1)⟩

theorem prep0 (R : List Bool) :
    zrun table 4 ⟨5,0,[],false::false::true::R⟩ =
      some (atR 0 4 [false,true,true,true] R) := by rfl

theorem pair0 (L R : List Bool) :
    zrun table 4 (atR 0 0 L (true::true::R)) =
      some (atR 0 2 (true::true::L) R) := by rfl

theorem turn0 (L : List Bool) :
    zrun table 4 (atR 0 0 L []) =
      some ⟨4,0,true::L,[false,true]⟩ := by rfl

theorem left0 (L R : List Bool) :
    zrun table 3 ⟨4,0,true::L,false::R⟩ =
      some ⟨4,-1,L,false::true::R⟩ := by rfl

theorem clear0 (R : List Bool) :
    zrun table 4 ⟨4,0,[false,true,true,true],false::R⟩ =
      some ⟨5,-4,[],zeros 5 ++ R⟩ := by rfl

theorem finish0 (R : List Bool) :
    zrun table 58 ⟨5,0,[],zeros 5 ++ true::true::R⟩ =
      some ⟨5,-4,[],zeros 2 ++ ones 9 ++ R⟩ := by rfl

theorem prep (h : Int) (R : List Bool) :
    zrun table 4 ⟨5,h,[],false::false::true::R⟩ =
      some (atR 0 (h+4) [false,true,true,true] R) := by
  have H := zrun_shift table h 4 ⟨5,0,[],false::false::true::R⟩
  rw [prep0] at H
  simpa [atR,shift,Int.add_comm] using H

theorem pair (h : Int) (L R : List Bool) :
    zrun table 4 (atR 0 h L (true::true::R)) =
      some (atR 0 (h+2) (true::true::L) R) := by
  have H := zrun_shift table h 4 (atR 0 0 L (true::true::R))
  rw [pair0] at H
  simpa [atR,shift,Int.add_comm] using H

theorem turn (h : Int) (L : List Bool) :
    zrun table 4 (atR 0 h L []) =
      some ⟨4,h,true::L,[false,true]⟩ := by
  have H := zrun_shift table h 4 (atR 0 0 L [])
  rw [turn0] at H
  simpa [atR,shift] using H

theorem left (h : Int) (L R : List Bool) :
    zrun table 3 ⟨4,h,true::L,false::R⟩ =
      some ⟨4,h-1,L,false::true::R⟩ := by
  have H := zrun_shift table h 3 ⟨4,0,true::L,false::R⟩
  rw [left0] at H
  simpa [shift,show -1+h=h-1 by omega] using H

theorem clear (h : Int) (R : List Bool) :
    zrun table 4 ⟨4,h,[false,true,true,true],false::R⟩ =
      some ⟨5,h-4,[],zeros 5 ++ R⟩ := by
  have H := zrun_shift table h 4 ⟨4,0,[false,true,true,true],false::R⟩
  rw [clear0] at H
  simpa [shift,show -4+h=h-4 by omega] using H

theorem finish (h : Int) (R : List Bool) :
    zrun table 58 ⟨5,h,[],zeros 5 ++ true::true::R⟩ =
      some ⟨5,h-4,[],zeros 2 ++ ones 9 ++ R⟩ := by
  have H := zrun_shift table h 58 ⟨5,0,[],zeros 5 ++ true::true::R⟩
  rw [finish0] at H
  simpa [shift,show -4+h=h-4 by omega] using H

theorem rightSweep (k : Nat) (h : Int) (L R : List Bool) :
    zrun table (4*k) (atR 0 h L (ones (2*k)++R)) =
      some (atR 0 (h+2*(k:Int)) (ones (2*k)++L) R) := by
  induction k generalizing h L with
  | zero => simp [ones,zrun]
  | succ k ih =>
    have H := join (pair h L (ones (2*k)++R)) (ih (h+2) (true::true::L))
    rw [show 4*(k+1)=4+4*k by omega]
    have hi : ones (2*(k+1))++R = true::true::(ones (2*k)++R) := by
      rw [show 2*(k+1)=2+2*k by omega,ones_add,List.append_assoc];rfl
    have hl : ones (2*k)++true::true::L = ones (2*(k+1))++L := by
      rw [show 2*(k+1)=2*k+2 by omega,ones_add,List.append_assoc];rfl
    simpa only [hi,hl,Int.natCast_succ,show h+2+2*(k:Int)=h+2*((k:Int)+1) by omega] using H

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

theorem growth (k : Nat) (h : Int) :
    zrun table (10*k+73) (X k h) = some (X (k+4) (h-5)) := by
  have h1 := prep h (ones (2*k))
  have h2 := rightSweep k (h+4) [false,true,true,true] []
  simp only [List.append_nil] at h2
  have h3 := turn (h+4+2*(k:Int)) (ones (2*k)++[false,true,true,true])
  have h4 := leftSweep (2*k+1) (h+4+2*(k:Int)) [false,true,true,true] [true]
  have hl : true::(ones (2*k)++[false,true,true,true]) =
      ones (2*k+1)++[false,true,true,true] := by
    rw [show 2*k+1=1+2*k by omega,ones_add,List.append_assoc];rfl
  have hr : ones (2*k+1)++[true] = true::true::ones (2*k) := by
    rw [show 2*k+1=1+2*k by omega,ones_add,List.append_assoc]
    change true::(ones (2*k)++[true]) = true::true::ones (2*k)
    have he : ones (2*k)++[true] = true::ones (2*k) := by
      rw [show [true] = ones 1 by rfl,←ones_add, Nat.add_comm (2*k) 1,ones_add];rfl
    rw [he]
  have hh : h+4+2*(k:Int)-((2*k+1:Nat):Int)=h+3 := by omega
  rw [←hl,hr,hh] at h4
  have h5 := clear (h+3) (true::true::ones (2*k))
  have h6 := finish (h-1) (ones (2*k))
  have ha : h+3-4=h-1 := by omega
  rw [ha] at h5
  have H := join (join (join (join (join h1 h2) h3) h4) h5) h6
  have hx : zeros 2 ++ ones (2*k+1) = false::false::true::ones (2*k) := by
    rw [show 2*k+1=1+2*k by omega,ones_add];rfl
  have hy : zeros 2 ++ ones 9 ++ ones (2*k) = zeros 2 ++ ones (2*(k+4)+1) := by
    rw [List.append_assoc,←ones_add,show 9+2*k=2*(k+4)+1 by omega]
  simpa only [X,hx,hy,show 4+4*k+4+3*(2*k+1)+4+58=10*k+73 by omega,
    show h-1-4=h-5 by omega] using H

def start : Z := ⟨0,0,[],[]⟩
theorem first : zrun table 6120 start = some (X 61 (-98)) := by decide +kernel

theorem arbitraryRun (n : Nat) : ∃ t k h, n ≤ t ∧ zrun table t start = some (X k h) := by
  induction n with
  | zero => exact ⟨6120,61,-98,by omega,first⟩
  | succ n ih =>
    obtain ⟨t,k,h,ht,hr⟩ := ih
    exact ⟨t+(10*k+73),k+4,h-5,by omega,join hr (growth k h)⟩

theorem start_embed : embed start = blank := by
  unfold embed start blank
  congr 1
  funext x
  simp [atCell]

theorem table_never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,k,h,ht,hr⟩ := arbitraryRun n
  have H := zrun_sound table m hm t _ _ hr
  rw [start_embed] at H
  rw [show t=n+(t-n) by omega,run_append] at H
  cases he : run m n blank with
  | none =>
    have he' : run m n (emptyAt 0) = none := he
    simp [he'] at H
  | some c => rfl

def ctr : PartialMachine := FAR.fromCodes [7,21,11,1,14,24,3,16,20,11,15,20]
theorem same : ctr = table :=
  BB6.Agent31ThreeHole.tableOK_sound _ _ (by decide +kernel)
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  table_never m (by simpa only [← same] using hm)

#print axioms growth
#print axioms first
#print axioms arbitraryRun
#print axioms never
end BB6Coverage.Agent14E0LFResidual10338
