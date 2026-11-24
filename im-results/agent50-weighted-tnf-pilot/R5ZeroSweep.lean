import R5Sweep

set_option maxRecDepth 24000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent50R5ZeroSweep
open BB6Coverage Agent50Zipper
open BB6Coverage.Agent50R5Sweep

def K : List Bool := [false,true,false]
def J : List Bool := [true,false,false]
def U : List Bool := [false,false,true]
def V : List Bool := [false,true,false,true,false,true]
def I : List Bool := [false,true,false,false]
def oddTail : List Bool := [true,true,false,false,false]
def evenTail : List Bool := [false,false]

def oddFamily (n : Nat) (h : Int) : Z := ⟨1,h,P++rep K (n+1)++oddTail,[]⟩
def evenFamily (n : Nat) (h : Int) : Z := ⟨1,h,P++rep K (n+3)++evenTail,[]⟩

theorem pre0 (L : List Bool) : zrun (table false) 6 ⟨1,0,P++L,[]⟩ = some ⟨1,-4,L,Q⟩ := by rfl

theorem left0 (L S : List Bool) : zrun (table false) 3 ⟨1,0,K++L,S⟩ = some ⟨1,-3,L,K++S⟩ := by rfl

theorem oddTurn0 (S : List Bool) : zrun (table false) 4 ⟨1,0,oddTail,I++S⟩ = some ⟨1,4,V++[false,false,false],S⟩ := by rfl

theorem evenTurn0 (S : List Bool) : zrun (table false) 14 ⟨1,0,evenTail,I++S⟩ = some ⟨1,4,[false,true,true,false,true,false],S⟩ := by rfl

theorem evenFirst0 (S : List Bool) : zrun (table false) 11 ⟨1,0,[false,true,true,false,true,false],J++S⟩ = some ⟨1,3,[false,true,false,true,true,true,false,false,false],S⟩ := by rfl

theorem evenSecond0 (S : List Bool) : zrun (table false) 9 ⟨1,0,[false,true,false,true,true,true,false,false,false],J++S⟩ = some ⟨1,3,V++false::oddTail,S⟩ := by rfl

theorem right0 (L S : List Bool) : zrun (table false) 9 ⟨1,0,V++L,J++S⟩ = some ⟨1,3,V++U++L,S⟩ := by rfl

theorem finish0 (L : List Bool) : zrun (table false) 40 ⟨1,0,V++L,T⟩ = some ⟨1,6,P++[false,true]++U++U++L,[]⟩ := by rfl

theorem prelude (h : Int) (L : List Bool) : zrun (table false) 6 ⟨1,h,P++L,[]⟩ = some ⟨1,h-4,L,Q⟩ := by
  have H := zrun_shift (table false) h 6 ⟨1,0,P++L,[]⟩
  rw [pre0] at H
  simpa [shift,show -4+h=h-4 by omega] using H

theorem leftOne (h : Int) (L S : List Bool) : zrun (table false) 3 ⟨1,h,K++L,S⟩ = some ⟨1,h-3,L,K++S⟩ := by
  have H := zrun_shift (table false) h 3 ⟨1,0,K++L,S⟩
  rw [left0] at H
  simpa [shift,show -3+h=h-3 by omega] using H

theorem leftSweep (n : Nat) (h : Int) (L S : List Bool) :
    zrun (table false) (3*n) ⟨1,h,rep K n++L,S⟩ = some ⟨1,h-3*(n:Int),L,rep K n++S⟩ := by
  induction n generalizing h S with
  | zero => simp [rep,zrun]
  | succ n ih =>
    have H := join (leftOne h (rep K n++L) S) (ih (h-3) (K++S))
    rw [show 3*(n+1)=3+3*n by omega]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep K n) K S,rep_snoc K n,
      Int.natCast_succ,show h-3-3*(n:Int)=h-3*((n:Int)+1) by omega] using H

theorem turnWord (n : Nat) : rep K (n+1)++Q = I++rep J n++T := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep, List.append_assoc,ih, List.append_assoc I (rep J n) T,← List.append_assoc K I,show K++I=I++J by rfl]
    simp only [rep,List.append_assoc]

theorem oddTurn (h : Int) (S : List Bool) : zrun (table false) 4 ⟨1,h,oddTail,I++S⟩ = some ⟨1,h+4,V++[false,false,false],S⟩ := by
  have H := zrun_shift (table false) h 4 ⟨1,0,oddTail,I++S⟩
  rw [oddTurn0] at H
  simpa [shift,Int.add_comm] using H

theorem evenTurn (h : Int) (S : List Bool) : zrun (table false) 14 ⟨1,h,evenTail,I++S⟩ = some ⟨1,h+4,[false,true,true,false,true,false],S⟩ := by
  have H := zrun_shift (table false) h 14 ⟨1,0,evenTail,I++S⟩
  rw [evenTurn0] at H
  simpa [shift,Int.add_comm] using H

theorem evenFirst (h : Int) (S : List Bool) : zrun (table false) 11 ⟨1,h,[false,true,true,false,true,false],J++S⟩ = some ⟨1,h+3,[false,true,false,true,true,true,false,false,false],S⟩ := by
  have H := zrun_shift (table false) h 11 ⟨1,0,[false,true,true,false,true,false],J++S⟩
  rw [evenFirst0] at H
  simpa [shift,Int.add_comm] using H

theorem evenSecond (h : Int) (S : List Bool) : zrun (table false) 9 ⟨1,h,[false,true,false,true,true,true,false,false,false],J++S⟩ = some ⟨1,h+3,V++false::oddTail,S⟩ := by
  have H := zrun_shift (table false) h 9 ⟨1,0,[false,true,false,true,true,true,false,false,false],J++S⟩
  rw [evenSecond0] at H
  simpa [shift,Int.add_comm] using H

theorem rightOne (h : Int) (L S : List Bool) : zrun (table false) 9 ⟨1,h,V++L,J++S⟩ = some ⟨1,h+3,V++U++L,S⟩ := by
  have H := zrun_shift (table false) h 9 ⟨1,0,V++L,J++S⟩
  rw [right0] at H
  simpa [shift,Int.add_comm] using H

theorem rightSweep (n : Nat) (h : Int) (L S : List Bool) :
    zrun (table false) (9*n) ⟨1,h,V++L,rep J n++S⟩ = some ⟨1,h+3*(n:Int),V++rep U n++L,S⟩ := by
  induction n generalizing h L with
  | zero => simp [rep,zrun]
  | succ n ih =>
    have H := join (rightOne h L (rep J n++S)) (ih (h+3) (U++L))
    rw [show 9*(n+1)=9+9*n by omega]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep U n) U L,rep_snoc U n,
      Int.natCast_succ,show h+3+3*(n:Int)=h+3*((n:Int)+1) by omega] using H

theorem finish (h : Int) (L : List Bool) : zrun (table false) 40 ⟨1,h,V++L,T⟩ = some ⟨1,h+6,P++[false,true]++U++U++L,[]⟩ := by
  have H := zrun_shift (table false) h 40 ⟨1,0,V++L,T⟩
  rw [finish0] at H
  simpa [shift,Int.add_comm] using H

theorem finishWord (n : Nat) (L : List Bool) : [false,true]++rep U n++false::L = rep K (n+1)++L := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep,rep,← List.append_assoc [false,true] U,show [false,true]++U=K++[false,true] by rfl]
    simpa only [List.append_assoc] using congrArg (K++·) ih

theorem oddGrowth (n : Nat) (h : Int) : zrun (table false) (53+12*n) (oddFamily n h) = some (evenFamily n (h+3)) := by
  let a := h-4-3*((n+1:Nat):Int)
  have h1 := prelude h (rep K (n+1)++oddTail)
  have h2 := leftSweep (n+1) (h-4) oddTail Q
  have h3 := oddTurn a (rep J n++T)
  rw [turnWord] at h2
  have h4 := rightSweep n (a+4) [false,false,false] T
  have h5 := finish (a+4+3*(n:Int)) (rep U n++[false,false,false])
  have H := join (join (join (join h1 h2) h3) h4) h5
  have hw : P++[false,true]++U++U++(rep U n++[false,false,false]) = P++rep K (n+3)++evenTail := by
    simpa only [rep,List.append_assoc,evenTail] using congrArg (P++·) (finishWord (n+2) evenTail)
  rw [hw] at H
  have ha : a+4+3*(n:Int)+6=h+3 := by dsimp [a]; omega
  simpa only [oddFamily,evenFamily,List.append_assoc,ha,show 6+3*(n+1)+4+9*n+40=53+12*n by omega] using H

theorem evenGrowth (n : Nat) (h : Int) : zrun (table false) (89+12*n) (evenFamily n h) = some (oddFamily (n+2) (h+3)) := by
  let a := h-4-3*((n+3:Nat):Int)
  have h1 := prelude h (rep K (n+3)++evenTail)
  have h2 := leftSweep (n+3) (h-4) evenTail Q
  rw [turnWord (n+2)] at h2
  have h3 := evenTurn a (rep J (n+2)++T)
  have h4 := evenFirst (a+4) (rep J (n+1)++T)
  have h5 := evenSecond (a+4+3) (rep J n++T)
  have h6 := rightSweep n (a+4+3+3) (false::oddTail) T
  have h7 := finish (a+4+3+3+3*(n:Int)) (rep U n++false::oddTail)
  have H := join (join (join (join (join (join h1 h2) h3) h4) h5) h6) h7
  have hw : P++[false,true]++U++U++(rep U n++false::oddTail) = P++rep K (n+3)++oddTail := by
    simpa only [rep,List.append_assoc] using congrArg (P++·) (finishWord (n+2) oddTail)
  rw [hw] at H
  have ha : a+4+3+3+3*(n:Int)+6=h+3 := by dsimp [a]; omega
  simpa only [oddFamily,evenFamily,List.append_assoc,ha,show 6+3*(n+3)+14+11+9+9*n+40=89+12*n by omega] using H

theorem growth (n : Nat) (h : Int) : zrun (table false) (142+24*n) (oddFamily n h) = some (oddFamily (n+2) (h+6)) := by
  have H := join (oddGrowth n h) (evenGrowth n (h+3))
  simpa only [show 53+12*n+(89+12*n)=142+24*n by omega,show h+3+3=h+6 by omega] using H

theorem first : zrun (table false) 113 start = some (oddFamily 0 7) := by rfl

theorem arbitraryRun (n : Nat) : ∃ t k h, n ≤ t ∧
    zrun (table false) t start = some (oddFamily k h) := by
  induction n with
  | zero => exact ⟨113,0,7,by omega,first⟩
  | succ n ih =>
    obtain ⟨t,k,h,ht,hr⟩ := ih
    exact ⟨t+(142+24*k),k+2,h+6,by omega,join hr (growth k h)⟩

theorem never_zero (m : Machine) (hm : compatible (table false) m) : NeverHalts m := by
  intro n
  obtain ⟨t,k,h,ht,hr⟩ := arbitraryRun n
  have H := zrun_sound (table false) m hm t _ _ hr
  rw [Agent50R5Sweep.initial_embed] at H
  rw [show t=n+(t-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some c => rfl

#print axioms never_zero
end BB6Coverage.Agent50R5ZeroSweep
