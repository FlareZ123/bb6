import SparseZipper

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace BB6Coverage.Agent41Raw139E0OneLA
open BB6Coverage Agent50Zipper

/-- Exact partial table, F1 unassigned. -/
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨true,false,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,3⟩)
  | _,_ => none

def P : List Bool := [false,false,false,true]
def Q : List Bool := [true,false,true,true]
def K : List Bool := [false,true,false,false]

def rep (w : List Bool) : Nat → List Bool
  | 0 => []
  | n+1 => w ++ rep w n

theorem rep_snoc (w : List Bool) (n : Nat) : rep w n ++ w = w ++ rep w n := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp only [rep,List.append_assoc,ih]

def X (n : Nat) (h : Int) : Z := ⟨3,h,true::(rep P n++[false]),[true]⟩
def Y (n : Nat) (h : Int) : Z := ⟨3,h,true::(rep P n++[false,false,true]),[true]⟩

theorem left0 (L R : List Bool) :
    zrun table 8 ⟨3,0,true::(P++L),R⟩ = some ⟨3,-4,true::L,Q++R⟩ := by rfl

theorem blankTurn0 (R : List Bool) :
    zrun table 8 ⟨3,0,[true,false],R⟩ = some ⟨3,-4,[],Q++R⟩ := by rfl

theorem startRight0 (R : List Bool) :
    zrun table 2 ⟨3,0,[],R⟩ = some ⟨1,0,[true,true],R⟩ := by rfl

theorem right0 (L R : List Bool) :
    zrun table 4 ⟨1,0,true::L,Q++R⟩ = some ⟨1,4,true::(K++L),R⟩ := by rfl

theorem finish0 (L : List Bool) :
    zrun table 4 ⟨1,0,true::L,[true]⟩ = some ⟨3,2,true::false::false::L,[true]⟩ := by rfl

theorem special0 (R : List Bool) :
    zrun table 10 ⟨3,0,[true,false,false,true],R⟩ = some ⟨1,0,[true,false,true,false],R⟩ := by rfl

theorem leftOne (h : Int) (L R : List Bool) :
    zrun table 8 ⟨3,h,true::(P++L),R⟩ = some ⟨3,h-4,true::L,Q++R⟩ := by
  have H := zrun_shift table h 8 ⟨3,0,true::(P++L),R⟩
  rw [left0] at H
  simpa [shift,show -4+h=h-4 by omega] using H

theorem blankTurn (h : Int) (R : List Bool) :
    zrun table 8 ⟨3,h,[true,false],R⟩ = some ⟨3,h-4,[],Q++R⟩ := by
  have H := zrun_shift table h 8 ⟨3,0,[true,false],R⟩
  rw [blankTurn0] at H
  simpa [shift,show -4+h=h-4 by omega] using H

theorem startRight (h : Int) (R : List Bool) :
    zrun table 2 ⟨3,h,[],R⟩ = some ⟨1,h,[true,true],R⟩ := by
  have H := zrun_shift table h 2 ⟨3,0,[],R⟩
  rw [startRight0] at H
  simpa [shift] using H

theorem rightOne (h : Int) (L R : List Bool) :
    zrun table 4 ⟨1,h,true::L,Q++R⟩ = some ⟨1,h+4,true::(K++L),R⟩ := by
  have H := zrun_shift table h 4 ⟨1,0,true::L,Q++R⟩
  rw [right0] at H
  simpa [shift,Int.add_comm] using H

theorem finishRight (h : Int) (L : List Bool) :
    zrun table 4 ⟨1,h,true::L,[true]⟩ = some ⟨3,h+2,true::false::false::L,[true]⟩ := by
  have H := zrun_shift table h 4 ⟨1,0,true::L,[true]⟩
  rw [finish0] at H
  simpa [shift,Int.add_comm] using H

theorem specialTurn (h : Int) (R : List Bool) :
    zrun table 10 ⟨3,h,[true,false,false,true],R⟩ = some ⟨1,h,[true,false,true,false],R⟩ := by
  have H := zrun_shift table h 10 ⟨3,0,[true,false,false,true],R⟩
  rw [special0] at H
  simpa [shift] using H

theorem leftSweep (n : Nat) (h : Int) (L R : List Bool) :
    zrun table (8*n) ⟨3,h,true::(rep P n++L),R⟩ =
      some ⟨3,h-4*(n:Int),true::L,rep Q n++R⟩ := by
  induction n generalizing h R with
  | zero => simp [rep,zrun]
  | succ n ih =>
    have H := join (leftOne h (rep P n++L) R) (ih (h-4) (Q++R))
    rw [show 8*(n+1)=8+8*n by omega]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep Q n) Q R,rep_snoc Q n,
      Int.natCast_succ,show h-4-4*(n:Int)=h-4*((n:Int)+1) by omega] using H

theorem rightSweep (n : Nat) (h : Int) (L R : List Bool) :
    zrun table (4*n) ⟨1,h,true::L,rep Q n++R⟩ =
      some ⟨1,h+4*(n:Int),true::(rep K n++L),R⟩ := by
  induction n generalizing h L with
  | zero => simp [rep,zrun]
  | succ n ih =>
    have H := join (rightOne h L (rep Q n++R)) (ih (h+4) (K++L))
    rw [show 4*(n+1)=4+4*n by omega]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep K n) K L,rep_snoc K n,
      Int.natCast_succ,show h+4+4*(n:Int)=h+4*((n:Int)+1) by omega] using H

theorem rotate (n : Nat) (L : List Bool) :
    [false,false] ++ (rep K n ++ L) = rep P n ++ ([false,false] ++ L) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      [false,false] ++ (rep K (n+1) ++ L) =
          ([false,false] ++ K) ++ (rep K n ++ L) := by simp [rep,List.append_assoc]
      _ = P ++ ([false,false] ++ (rep K n ++ L)) := by
        rw [show [false,false] ++ K = P ++ [false,false] by rfl]
        simp [List.append_assoc]
      _ = P ++ (rep P n ++ ([false,false] ++ L)) := by rw [ih]
      _ = rep P (n+1) ++ ([false,false] ++ L) := by simp [rep,List.append_assoc]

theorem growthXY (n : Nat) (h : Int) :
    zrun table (12*n+18) (X n h) = some (Y (n+1) (h+2)) := by
  let a := h-4*(n:Int)
  let b := a-4
  have h1 := leftSweep n h [false] [true]
  have h2 := blankTurn a (rep Q n++[true])
  have h3 := startRight b (rep Q (n+1)++[true])
  have h4 := rightSweep (n+1) b [true] [true]
  have h5 := finishRight (b+4*((n+1:Nat):Int)) (rep K (n+1)++[true])
  have H := join (join (join (join h1 h2) h3) h4) h5
  have hw : true::false::false::(rep K (n+1)++[true]) =
      true::(rep P (n+1)++[false,false,true]) := by
    change true::([false,false]++(rep K (n+1)++[true])) = _
    rw [rotate]; rfl
  have hh : b+4*((n+1:Nat):Int)+2 = h+2 := by dsimp [a,b]; omega
  simpa only [X,Y,hw,hh,show 8*n+8+2+4*(n+1)+4=12*n+18 by omega] using H

theorem growthYX (n : Nat) (h : Int) :
    zrun table (12*n+14) (Y n h) = some (X (n+1) (h+2)) := by
  let a := h-4*(n:Int)
  have h1 := leftSweep n h [false,false,true] [true]
  have h2 := specialTurn a (rep Q n++[true])
  have h3 := rightSweep n a [false,true,false] [true]
  have h4 := finishRight (a+4*(n:Int)) (rep K n++[false,true,false])
  have H := join (join (join h1 h2) h3) h4
  have hw : true::false::false::(rep K n++[false,true,false]) =
      true::(rep P (n+1)++[false]) := by
    change true::([false,false]++(rep K n++[false,true,false])) = _
    rw [rotate]
    rw [show [false,false]++[false,true,false]=P++[false] by rfl,
      ← List.append_assoc,rep_snoc]
    rfl
  have hh : a+4*(n:Int)+2=h+2 := by dsimp [a]; omega
  simpa only [X,Y,hw,hh,show 8*n+10+4*n+4=12*n+14 by omega] using H

theorem growth (n : Nat) (h : Int) :
    zrun table (24*n+44) (X n h) = some (X (n+2) (h+4)) := by
  have H := join (growthXY n h) (growthYX (n+1) (h+2))
  simpa only [show 12*n+18+(12*(n+1)+14)=24*n+44 by omega,
    show h+2+2=h+4 by omega] using H

def start : Z := ⟨0,0,[],[]⟩
theorem first : zrun table 102 start = some (X 3 10) := by rfl

theorem start_embed : embed start = blank := by
  unfold embed start blank
  congr 1
  funext x
  simp [atCell]

theorem arbitraryRun (n : Nat) : ∃ t k h, n ≤ t ∧
    zrun table t start = some (X k h) := by
  induction n with
  | zero => exact ⟨102,3,10,by omega,first⟩
  | succ n ih =>
    obtain ⟨t,k,h,ht,hr⟩ := ih
    exact ⟨t+(24*k+44),k+2,h+4,by omega,join hr (growth k h)⟩

/-- Every completion of the unread F1 row is nonhalting on the original blank tape. -/
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,k,h,ht,hr⟩ := arbitraryRun n
  have H := zrun_sound table m hm t _ _ hr
  rw [start_embed] at H
  rw [show t=n+(t-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some c => rfl

#print axioms growth
#print axioms first
#print axioms arbitraryRun
#print axioms never
end BB6Coverage.Agent41Raw139E0OneLA
