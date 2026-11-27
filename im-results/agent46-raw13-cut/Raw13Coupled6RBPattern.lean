import SweepPumping
import FastFAR

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13Coupled6RBPattern
open BB6Coverage BB6Coverage.Agent31Pump

/-- 1RB1LD1RC1RB1LA1RE1LF0LA0RC0RB---1LA. F0 is unassigned. -/
def p : PartialMachine := FAR.fromCodes [7,14,11,7,2,19,22,0,9,5,24,2]
abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev B (L R : List Bool) : Z0 := ⟨1,L,R⟩
abbrev X : List Bool := [true,false]
abbrev Y : List Bool := [false,true]
abbrev U : List Bool := [true,true]
abbrev W : List Bool := [true,true,true,true]
abbrev Z : List Bool := [true,true,true,true,true,true,true,false]
abbrev S : List Bool := [false,true,false,true,false]
abbrev Tail : List Bool := [true,false,true,false,true,true]
abbrev T : List Bool := [false,true,false,true,false,true,true]
abbrev V : List Bool := [true,true,true]
abbrev H0 : List Bool := [false,true,false,true,true,true]
abbrev H1 : List Bool := [true,false,true,false,true,true,true]
abbrev H2 : List Bool := [true,true,true,true,true,true,true,false,true,true,true]
abbrev J : List Bool := [true,true,true,false]
abbrev G : List Bool := [false,true,true,true]
abbrev P : List Bool := W ++ [false]
abbrev Q : List Bool := [false] ++ W

theorem shift (n : Nat) : W ++ rep Q n ++ [false] = rep P (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      W ++ rep Q (n+1) ++ [false] = P ++ (W ++ rep Q n ++ [false]) := by
        simp only [rep,P,Q,List.append_assoc]
      _ = rep P (n+2) := by rw [ih] <;> rfl

theorem rotate0 (n : Nat) : [false] ++ rep P n = rep Q n ++ [false] := by
  simpa only [P,Q] using rotate false W n

theorem bOne (L R : List Bool) :
    run0 p 5 (B ([true]++L) (X++P++R)) =
      some (B ([true]++Q++L) (X++R)) := by rfl

theorem bPump (n : Nat) (L R : List Bool) :
    run0 p (5*n) (B ([true]++L) (X++rep P n++R)) =
      some (B ([true]++rep Q n++L) (X++R)) :=
  sweepR p 1 [true] X P Q 5 bOne n L R

theorem start1 (L R : List Bool) :
    run0 p 8 (A ([false]++L) (S++P++R)) =
      some (B ([true,false]++H1++L) (X++R)) := by rfl

theorem start2 (L R : List Bool) :
    run0 p 7 (A (H0++L) (J++P++R)) =
      some (B ([true,false]++H2++L) (X++R)) := by rfl

theorem end21 (L : List Bool) :
    run0 p 21 (B ([true]++L) (X++Tail)) =
      some (A (Z++W++L) [true]) := by rfl

theorem bFinish (k : Nat) (L : List Bool) :
    run0 p (5*k+21) (B ([true,false]++L) (X++rep P k++Tail)) =
      some (A (Z++rep P (k+1)++L) [true]) := by
  have h : run0 p (5*k) (B ([true,false]++L) (X++rep P k++Tail)) =
      some (B ([true]++rep Q k++([false]++L)) (X++Tail)) :=
    bPump k ([false]++L) Tail
  have g : run0 p 21 (B ([true]++rep Q k++([false]++L)) (X++Tail)) =
      some (A (Z++rep P (k+1)++L) [true]) := by
    rw [← shift k]
    simpa only [List.append_assoc] using end21 (rep Q k++[false]++L)
  exact join0 h g

theorem right1 (k : Nat) (L : List Bool) :
    run0 p (5*k+29) (A ([false]++L) (S++rep P (k+1)++Tail)) =
      some (A (Z++rep P (k+1)++H1++L) [true]) := by
  have h : run0 p 8 (A ([false]++L) (S++rep P (k+1)++Tail)) =
      some (B ([true,false]++(H1++L)) (X++rep P k++Tail)) := by
    simpa only [rep,List.append_assoc] using start1 L (rep P k++Tail)
  simpa only [List.append_assoc,show 8+(5*k+21)=5*k+29 by omega] using
    join0 h (bFinish k (H1++L))

theorem right2 (k : Nat) (L : List Bool) :
    run0 p (5*k+28) (A (H0++L) (J++rep P (k+1)++Tail)) =
      some (A (Z++rep P (k+1)++H2++L) [true]) := by
  have h : run0 p 7 (A (H0++L) (J++rep P (k+1)++Tail)) =
      some (B ([true,false]++(H2++L)) (X++rep P k++Tail)) := by
    simpa only [rep,List.append_assoc] using start2 L (rep P k++Tail)
  simpa only [List.append_assoc,show 7+(5*k+21)=5*k+28 by omega] using
    join0 h (bFinish k (H2++L))

theorem pairLeft (n : Nat) (L R : List Bool) :
    run0 p (2*n) (A (rep U n++L) R) =
      some (A L (rep Y n++R)) :=
  sweepL p 0 [] [] U Y 2 (by intro L R; rfl) n L R

theorem blockLeft (n : Nat) (L R : List Bool) :
    run0 p (5*n) (A (X++rep P n++L) R) =
      some (A (X++L) (rep Q n++R)) :=
  sweepL p 0 X [] P Q 5 (by intro L R; rfl) n L R

theorem turn (L R : List Bool) :
    run0 p 3 (A (X++[true]++L) R) = some (A L (V++R)) := by rfl

theorem drain (n : Nat) (L : List Bool) :
    run0 p (5*n+6) (A (Z++rep P n++L) [true]) =
      some (A (X++L) (rep Q n++T)) := by
  have h : run0 p 6 (A (Z++rep P n++L) [true]) =
      some (A (X++rep P n++L) T) := pairLeft 3 (X++rep P n++L) [true]
  simpa only [show 6+5*n=5*n+6 by omega] using join0 h (blockLeft n L T)

theorem turnWord (n : Nat) : V++(rep Q n++T) = J++rep P n++Tail := by
  change V++(rep Q n++([false]++Tail)) = _
  rw [← List.append_assoc (rep Q n) [false] Tail,← rotate0 n]
  rfl

theorem left1 (n : Nat) (L : List Bool) :
    run0 p (5*n+9) (A (Z++rep P n++H1++L) [true]) =
      some (A (H0++L) (J++rep P n++Tail)) := by
  have h : run0 p (5*n+6) (A (Z++rep P n++H1++L) [true]) =
      some (A (X++[true]++(H0++L)) (rep Q n++T)) := by
    simpa only [List.append_assoc] using drain n (H1++L)
  have g := turn (H0++L) (rep Q n++T)
  rw [turnWord] at g
  simpa only [show 5*n+6+3=5*n+9 by omega] using join0 h g

theorem lastWord (n : Nat) :
    rep Y 3++(V++(rep Q n++T)) = S++rep P (n+1)++Tail := by
  rw [turnWord,show rep P (n+1)=P++rep P n by rfl]
  simp only [List.append_assoc]

theorem left2 (n : Nat) (L : List Bool) :
    run0 p (5*n+15) (A (Z++rep P n++H2++L) [true]) =
      some (A (G++L) (S++rep P (n+1)++Tail)) := by
  have h : run0 p (5*n+6) (A (Z++rep P n++H2++L) [true]) =
      some (A (X++[true]++(rep U 3++G++L)) (rep Q n++T)) := by
    simpa only [List.append_assoc] using drain n (H2++L)
  have g := turn (rep U 3++G++L) (rep Q n++T)
  have f := pairLeft 3 (G++L) (V++(rep Q n++T))
  have f' : run0 p 6 (A (rep U 3++G++L) (V++(rep Q n++T))) =
      some (A (G++L) (S++rep P (n+1)++Tail)) := by
    simpa only [List.append_assoc, lastWord] using f
  simpa only [show 5*n+6+3+6=5*n+15 by omega] using join0 (join0 h g) f'

/-- Exact return on an arbitrary untouched left tail, not just the blank orbit. -/
theorem advanceAux (k : Nat) (L : List Bool) :
    run0 p (20*k+91) (A ([false]++L) (S++rep P (k+1)++Tail)) =
      some (A (G++L) (S++rep P (k+2)++Tail)) := by
  have h := join0 (right1 k L) (left1 (k+1) L)
  have g := join0 (right2 k L) (left2 (k+1) L)
  simpa only [show (5*k+29+(5*(k+1)+9))+(5*k+28+(5*(k+1)+15))=20*k+91 by omega] using join0 h g

def root (n : Nat) : Z0 :=
  A ([false]++rep V n++[true,true,true,true,false,true,true,true]) (S++rep P (n+2)++Tail)

theorem seed : run0 p 223 (A [] []) = some (root 0) := by rfl

theorem advance (n : Nat) : run0 p (20*n+111) (root n) = some (root (n+1)) := by
  have h := advanceAux (n+1) (rep V n++[true,true,true,true,false,true,true,true])
  simpa only [root,rep,List.append_assoc,show 20*(n+1)+91=20*n+111 by omega] using h

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  never_of_growth p root 223 (fun n => 20*n+111) seed (fun n => by omega) advance m hm

#print axioms advanceAux
#print axioms advance
#print axioms never
end BB6.Agent46Raw13Coupled6RBPattern
