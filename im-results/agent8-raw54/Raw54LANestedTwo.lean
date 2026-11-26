import SweepPumping
import Raw54RAClosedCore
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace BB6.Agent8Raw54.LA.M119
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,true,2⟩)
  | _,_ => none

def ones : List Bool := [true,true,true]
def zeros : List Bool := [false,false,false]
def stop : List Bool := [false,true,true]
def mark : List Bool := [false,true,true,true,false,true]
def D (n : Nat) (L R : List Bool) : Z0 := ⟨3,[false,false,true]++rep ones n++mark++L,R⟩
def A (n : Nat) (L R : List Bool) : Z0 := ⟨0,[false,true,true]++rep ones n++mark++L,R⟩

theorem prep (n : Nat) (L R : List Bool) :
    run0 table (3+3*n+1) (D n L R) = some ⟨0,mark.tail++L,true::(rep zeros n++stop++R)⟩ := by
  have h0 : run0 table 3 (D n L R) = some ⟨4,rep ones n++mark++L,stop++R⟩ := by rfl
  have h1 : run0 table (3*n) ⟨4,rep ones n++mark++L,stop++R⟩ = some ⟨4,mark++L,rep zeros n++stop++R⟩ := by
    simpa only [List.nil_append,List.append_assoc] using sweepL table 4 [] [] ones zeros 3
      (by intro X Y; rfl) n (mark++L) (stop++R)
  have h2 : run0 table 1 ⟨4,mark++L,rep zeros n++stop++R⟩ =
    some ⟨0,mark.tail++L,true::(rep zeros n++stop++R)⟩ := by rfl
  exact join0 (join0 h0 h1) h2

theorem zeroReturn (L R : List Bool) : run0 table 12 (D 0 L R) = some (A 0 L R) := by rfl

theorem more (n : Nat) (L R : List Bool) :
    run0 table (3+3*(n+1)+1+6) (D (n+1) L R) = some (D 0 L (rep zeros n++stop++R)) := by
  have h : run0 table 6 ⟨0,mark.tail++L,true::(rep zeros (n+1)++stop++R)⟩ =
    some (D 0 L (rep zeros n++stop++R)) := by
    cases n <;> rfl
  exact join0 (prep (n+1) L R) h

theorem aStop (n : Nat) (L R : List Bool) : run0 table 5 (A n L (stop++R)) = some (A (n+1) L R) := by rfl
theorem aMore (n : Nat) (L R : List Bool) : run0 table 3 (A n L (zeros++R)) = some (D (n+1) L R) := by rfl

def Returns (n : Nat) : Prop := ∀ L R, ∃ t, run0 table t (D n L R) = some (A n L R)
theorem drain (N j k : Nat) (L R : List Bool) (lower : ∀ i, i < N → Returns i) (bound : j+k < N) :
    ∃ t, run0 table t (A j L (rep zeros k++stop++R)) = some (A (j+k+1) L R) := by
  induction k generalizing j with
  | zero => exact ⟨5,aStop j L R⟩
  | succ k ih =>
    have h := aMore j L (rep zeros k++stop++R)
    obtain ⟨u,hu⟩ := lower (j+1) (by omega) L (rep zeros k++stop++R)
    obtain ⟨t,ht⟩ := ih (j+1) (by omega)
    have H := join0 (join0 h hu) ht
    rw [show j+1+k+1=j+(k+1)+1 by omega] at H
    exact ⟨3+u+t,H⟩

theorem returns (n : Nat) : Returns n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro L R
    cases n with
    | zero => exact ⟨12,zeroReturn L R⟩
    | succ k =>
      have h := more k L R
      have h0 := zeroReturn L (rep zeros k++stop++R)
      obtain ⟨t,ht⟩ := drain (k+1) 0 k L R ih (by omega)
      rw [Nat.zero_add] at ht
      exact ⟨_,join0 (join0 h h0) ht⟩

theorem sectionReturn (n : Nat) : ∃ t, 0 < t ∧ run0 table t (D n [] []) = some (D (n+1) [] []) := by
  obtain ⟨t,h⟩ := returns n [] []
  have h' : run0 table 3 (A n [] []) = some (D (n+1) [] []) := by rfl
  exact ⟨t+3,by omega,join0 h h'⟩
theorem entry : run0 table 33 ⟨0,[],[]⟩ = some (D 1 [] []) := by rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply BB6.Agent8Raw54.RAClosed.neverOfSection table Nat (fun n => D n [] []) 1 33 entry _ m hm
  intro n
  obtain ⟨t,hp,h⟩ := sectionReturn n
  exact ⟨t,n+1,hp,h⟩
#print axioms never
end BB6.Agent8Raw54.LA.M119

namespace BB6.Agent8Raw54.LA.M138
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none

def ones : List Bool := [true,true]
def zeros : List Bool := [false,false]
def mark : List Bool := [false,false,false,true,false,false]
def D (n : Nat) (L R : List Bool) : Z0 := ⟨3,[false,false,true]++rep ones n++mark++L,R⟩
def C (n : Nat) (L R : List Bool) : Z0 := ⟨2,[true]++rep ones (n+1)++mark++L,R⟩
def A (L R : List Bool) : Z0 := ⟨0,[false,true]++mark++L,R⟩

theorem prep (n : Nat) (L R : List Bool) :
    run0 table (3+2*(n+1)+1+5) (D (n+1) L R) = some (A L (rep zeros n++[false,true,true]++R)) := by
  have h0 : run0 table 3 (D (n+1) L R) = some ⟨4,rep ones (n+1)++mark++L,[false,true,true]++R⟩ := by rfl
  have h1 : run0 table (2*(n+1)) ⟨4,rep ones (n+1)++mark++L,[false,true,true]++R⟩ =
    some ⟨4,mark++L,rep zeros (n+1)++[false,true,true]++R⟩ := by
    simpa only [List.nil_append,List.append_assoc] using sweepL table 4 [] [] ones zeros 2
      (by intro X Y; rfl) (n+1) (mark++L) ([false,true,true]++R)
  have h2 : run0 table 1 ⟨4,mark++L,rep zeros (n+1)++[false,true,true]++R⟩ =
    some ⟨0,mark.tail++L,true::(rep zeros (n+1)++[false,true,true]++R)⟩ := by rfl
  have h3 : run0 table 5 ⟨0,mark.tail++L,true::(rep zeros (n+1)++[false,true,true]++R)⟩ =
    some (A L (rep zeros n++[false,true,true]++R)) := by rfl
  exact join0 (join0 (join0 h0 h1) h2) h3

theorem aStop (L R : List Bool) : run0 table 3 (A L ([false,true,true]++R)) = some (C 1 L R) := by rfl
theorem aMore (L R : List Bool) : run0 table 3 (A L ([false,false,false]++R)) = some (D 1 L R) := by rfl
theorem cStop (n : Nat) (L R : List Bool) : run0 table 2 (C n L (ones++R)) = some (C (n+1) L R) := by rfl
theorem cMore (n : Nat) (L R : List Bool) : run0 table 2 (C n L (zeros++R)) = some (D (n+1) L R) := by rfl

def Returns (n : Nat) : Prop := ∀ L R, ∃ t, run0 table t (D n L R) = some (C n L R)
theorem drain (N j k : Nat) (L R : List Bool) (lower : ∀ i, 0 < i → i < N → Returns i)
    (hj : 0 < j) (bound : j+k < N) :
    ∃ t, run0 table t (C j L (rep zeros k++ones++R)) = some (C (j+k+1) L R) := by
  induction k generalizing j with
  | zero => exact ⟨2,cStop j L R⟩
  | succ k ih =>
    have h := cMore j L (rep zeros k++ones++R)
    obtain ⟨u,hu⟩ := lower (j+1) (by omega) (by omega) L (rep zeros k++ones++R)
    obtain ⟨t,ht⟩ := ih (j+1) (by omega) (by omega)
    have H := join0 (join0 h hu) ht
    rw [show j+1+k+1=j+(k+1)+1 by omega] at H
    exact ⟨2+u+t,H⟩

theorem returns (n : Nat) (hn : 0 < n) : Returns n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => omega
    | succ k =>
      intro L R
      have h := prep k L R
      cases k with
      | zero => exact ⟨_,join0 h (aStop L R)⟩
      | succ j =>
        have e : rep zeros (j+1)++[false,true,true]++R = [false,false,false]++(rep zeros j++ones++R) := by
          simp only [rep,List.append_assoc]
          exact congrArg (fun T => false::false::T) ((moveCut [] (ones++R) [false] false j).symm)
        rw [e] at h
        have h0 := aMore L (rep zeros j++ones++R)
        have lower : ∀ i, 0 < i → i < j+2 → Returns i := fun i hi hil => ih i hil hi
        obtain ⟨u,hu⟩ := lower 1 (by omega) (by omega) L (rep zeros j++ones++R)
        obtain ⟨t,ht⟩ := drain (j+2) 1 j L R lower (by omega) (by omega)
        have H := join0 (join0 (join0 h h0) hu) ht
        rw [show 1+j+1=j+1+1 by omega] at H
        exact ⟨_,H⟩

theorem sectionReturn (n : Nat) : ∃ t, 0 < t ∧ run0 table t (D (n+1) [] []) = some (D (n+2) [] []) := by
  obtain ⟨t,h⟩ := returns (n+1) (by omega) [] []
  have h' : run0 table 2 (C (n+1) [] []) = some (D (n+2) [] []) := by rfl
  exact ⟨t+2,by omega,join0 h h'⟩
theorem entry : run0 table 22 ⟨0,[],[]⟩ = some (D 1 [] []) := by rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply BB6.Agent8Raw54.RAClosed.neverOfSection table Nat (fun n => D (n+1) [] []) 0 22 entry _ m hm
  intro n
  obtain ⟨t,hp,h⟩ := sectionReturn n
  exact ⟨t,n+1,hp,h⟩
#print axioms never
end BB6.Agent8Raw54.LA.M138
