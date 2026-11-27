import SweepPumping
import FastFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13Coupled6RDSweep
open BB6Coverage BB6Coverage.Agent31Pump

def p (d f : Bool) : PartialMachine := FAR.fromCodes [7,14,11,3,2,19,if d then 22 else 20,0,5,15,24,if d then (if f then 14 else 6) else 11]
abbrev X : List Bool := [true,false]
abbrev Y : List Bool := [false,true]
abbrev U : List Bool := [true,true]
abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩

theorem rep_add (P : List Bool) (a b : Nat) : rep P (a+b) = rep P a ++ rep P b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [Nat.succ_add,rep,ih,rep]; simp only [List.append_assoc]

theorem left (d f : Bool) (n : Nat) (L R : List Bool) :
    run0 (p d f) (2*n) (A (rep U n++L) R) = some (A L (rep Y n++R)) :=
  sweepL _ 0 [] [] U Y 2 (by intro L R; cases d <;> cases f <;> rfl) n L R

theorem right (d f : Bool) (n : Nat) (L R : List Bool) :
    run0 (p d f) (2*n) (A ([false]++L) (rep X n++R)) = some (A ([false]++rep U n++L) R) :=
  sweepR _ 0 [false] [] X U 2 (by intro L R; cases d <;> cases f <;> rfl) n L R

theorem start3 (d f : Bool) (L : List Bool) :
    run0 (p d f) 3 (A ([false]++L) []) = some (A (U++L) [true]) := by
  cases d <;> cases f <;> rfl

theorem first5 (d f : Bool) (L R : List Bool) :
    run0 (p d f) 5 (A ([false]++L) (rep Y 2++[false]++R)) = some (A ([false,true,false,true,true,true]++L) R) := by
  cases d <;> cases f <;> rfl

theorem turn (d f : Bool) (L R : List Bool) :
    run0 (p d f) 2 (A ([false]++L) (U++R)) = some (A ([true,true,true]++L) R) := by
  cases d <;> cases f <;> rfl

theorem turnEnd (d f : Bool) (L : List Bool) :
    run0 (p d f) 2 (A ([false]++L) [true]) = some (A ([false,true,true]++L) []) := by
  cases d <;> cases f <;> rfl

theorem bridge (d f : Bool) (R : List Bool) :
    run0 (p d f) (if d && f then 14 else 16) (A ([true,false]++rep U 6) R) = some (A [] (rep Y 6++U++R)) := by
  cases d <;> cases f <;> rfl

def root (k : Nat) : Z0 := A ([false]++rep U (2*k+1)++[true,false]++rep U 6) []

theorem stage0 (d f : Bool) (k : Nat) :
    run0 (p d f) (3+2*(2*k+2)+(if d && f then 14 else 16)) (root k) =
      some (A [] (rep Y 6++U++rep Y (2*k+2)++[true])) := by
  have h := start3 d f (rep U (2*k+1)++[true,false]++rep U 6)
  have h' : run0 (p d f) 3 (root k) = some (A (rep U (2*k+2)++([true,false]++rep U 6)) [true]) := by
    simpa only [root,rep,List.append_assoc] using h
  have g := join0 h' (left d f (2*k+2) ([true,false]++rep U 6) [true])
  simpa only [List.append_assoc] using join0 g (bridge d f (rep Y (2*k+2)++[true]))

theorem stage1 (d f : Bool) (b : Nat) :
    run0 (p d f) 23 (A [] (rep Y 6++U++rep Y b++[true])) =
      some (A ([false]++rep U 1++[true]) (rep Y 5++[true]++rep Y b++[true])) := by
  have h : run0 (p d f) 5 (A [] (rep Y 6++U++rep Y b++[true])) =
      some (A ([false]++[true,false,true,true,true]) (rep X 3++U++[true]++rep Y b++[true])) := by
    cases d <;> cases f <;> rfl
  have g := join0 h (right d f 3 [true,false,true,true,true] (U++[true]++rep Y b++[true]))
  have g' := join0 g (turn d f (rep U 3++[true,false,true,true,true]) ([true]++rep Y b++[true]))
  have H := join0 g' (left d f 5 ([false]++rep U 1++[true]) ([true]++rep Y b++[true]))
  simpa only [List.append_assoc] using H

theorem stage2 (d f : Bool) (b : Nat) :
    run0 (p d f) 19 (A ([false]++rep U 1++[true]) (rep Y 5++[true]++rep Y b++[true])) =
      some (A ([false]++rep U 3) (rep Y (b+4)++[true])) := by
  have h : run0 (p d f) 5 (A ([false]++rep U 1++[true]) (rep Y 5++[true]++rep Y b++[true])) =
      some (A ([false]++[true,false]++rep U 3) (rep X 2++U++rep Y b++[true])) := by
    cases d <;> cases f <;> rfl
  have g := join0 h (right d f 2 ([true,false]++rep U 3) (U++rep Y b++[true]))
  have g' := join0 g (turn d f (rep U 2++[true,false]++rep U 3) (rep Y b++[true]))
  have H := join0 g' (left d f 4 ([false]++rep U 3) (rep Y b++[true]))
  have ww : rep Y 4++rep Y b = rep Y (b+4) := by rw [Nat.add_comm b 4,rep_add]
  simpa only [←List.append_assoc,ww] using H

theorem stage3 (d f : Bool) (b : Nat) :
    run0 (p d f) (4*b+15) (A ([false]++rep U 3) (rep Y (b+4)++[true])) =
      some (A ([false]++rep U 4++[true]) (rep Y (b+3))) := by
  have h := first5 d f (rep U 3) (rep X (b+1)++U)
  have w : rep Y (b+4)++[true] = rep Y 2++[false]++(rep X (b+1)++U) := by
    rw [show b+4=2+(b+2) by omega,rep_add]
    change rep Y 2++rep Y (b+2)++[true] = _
    rw [show b+2=(b+1)+1 by omega,rep]
    have ww : [true]++rep Y (b+1)=rep X (b+1)++[true] := rotate true [false] (b+1)
    change rep Y 2 ++ [false] ++ [true] ++ rep Y (b+1) ++ [true] = _
    rw [show rep Y 2 ++ [false] ++ [true] ++ rep Y (b+1) ++ [true] = rep Y 2 ++ [false] ++ (([true] ++ rep Y (b+1)) ++ [true]) by simp only [List.append_assoc],ww]
    simp only [List.append_assoc]
    rfl
  have h' : run0 (p d f) 5 (A ([false]++rep U 3) (rep Y (b+4)++[true])) =
      some (A ([false]++[true,false]++rep U 4++[true]) (rep X (b+1)++U)) := by
    rw [w]; exact h
  have g := join0 h' (right d f (b+1) ([true,false]++rep U 4++[true]) U)
  have hturn := turn d f (rep U (b+1)++[true,false]++rep U 4++[true]) []
  simp only [List.append_assoc,List.append_nil] at hturn g
  have g' := join0 g hturn
  have wl : [true,true,true]++(rep U (b+1)++([true,false]++(rep U 4++[true]))) = rep U (b+3)++([false]++rep U 4++[true]) := by
    have ww : [true]++rep U (b+1)=rep U (b+1)++[true] := rotate true [true] (b+1)
    have wr : rep U (b+3)=U++rep U (b+1)++U := by
      rw [show b+3=1+(b+1)+1 by omega,rep_add,rep_add]
      rfl
    rw [wr]
    calc
      _ = U++([true]++rep U (b+1))++([true,false]++(rep U 4++[true])) := by simp only [List.append_assoc]; rfl
      _ = _ := by rw [ww]; simp only [List.append_assoc]; rfl
  rw [wl] at g'
  have H := join0 g' (left d f (b+3) ([false]++rep U 4++[true]) [])
  simpa only [List.append_nil,show 5+2*(b+1)+2+2*(b+3)=4*b+15 by omega] using H

theorem stage4 (d f : Bool) (k : Nat) :
    run0 (p d f) (2*(2*k+2)+7) (A ([false]++rep U 4++[true]) (rep Y ((2*k+2)+3))) = some (root (k+1)) := by
  let b := 2*k+2
  have ww : [true]++rep Y b = rep X b++[true] := rotate true [false] b
  have w : rep Y (b+3) = rep Y 2++[false]++(rep X b++[true]) := by
    rw [show b+3=2+(b+1) by omega,rep_add,rep]
    change rep Y 2++[false]++([true]++rep Y b) = _
    rw [ww]
    rfl
  have h := first5 d f (rep U 4++[true]) (rep X b++[true])
  have h' : run0 (p d f) 5 (A ([false]++rep U 4++[true]) (rep Y (b+3))) =
      some (A ([false]++[true,false]++rep U 6) (rep X b++[true])) := by
    rw [w]; exact h
  have g := join0 h' (right d f b ([true,false]++rep U 6) [true])
  have he := turnEnd d f (rep U b++[true,false]++rep U 6)
  simp only [List.append_assoc] at g he
  have H := join0 g he
  have wl : [false,true,true]++(rep U b++([true,false]++rep U 6)) = [false]++rep U (b+1)++[true,false]++rep U 6 := by
    simp only [rep,List.append_assoc,U,List.cons_append,List.nil_append]
  rw [wl] at H
  simpa only [root,List.append_assoc,show 2*(k+1)+1=b+1 by omega,show 5+2*b+2=2*b+7 by omega] using H

theorem rootGrowth (d f : Bool) (k : Nat) : ∃ n, 0<n ∧ run0 (p d f) n (root k)=some (root (k+1)) := by
  have h0 := stage0 d f k
  have h1 := join0 h0 (stage1 d f (2*k+2))
  have h2 := join0 h1 (stage2 d f (2*k+2))
  have h3 := join0 h2 (stage3 d f (2*k+2))
  have h4 := join0 h3 (stage4 d f k)
  exact ⟨_,by omega,h4⟩

theorem seed (d f : Bool) : run0 (p d f) (if d && f then 153 else 161) (A [] []) = some (root 0) := by
  cases d <;> cases f <;> rfl

theorem never (d f : Bool) (m : Machine) (hm : compatible (p d f) m) : NeverHalts m := by
  let cost := fun k => Classical.choose (rootGrowth d f k)
  exact never_of_growth (p d f) root (if d && f then 153 else 161) cost (seed d f)
    (fun k => (Classical.choose_spec (rootGrowth d f k)).1)
    (fun k => (Classical.choose_spec (rootGrowth d f k)).2) m hm

#print axioms rootGrowth
#print axioms never
end BB6.Agent46Raw13Coupled6RDSweep
