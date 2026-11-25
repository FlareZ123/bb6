import Agent46AutoPump
import FastFAR

namespace BB6.Agent46Raw13OneLC.Binary
open BB6Coverage BB6Coverage.Agent31Pump
open BB6Coverage.Agent31Pump.Auto (knownRun knownRun_sound extend)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def p : PartialMachine := FAR.fromCodes [7,10,11,12,2,5,10,17,21,24,13,23]
def T : List Bool := [false,false,false,false,true,false,false]
def X : List Bool := true::T
def Y : List Bool := [false,false,false,true,false,false]
def Q : List Bool := [true,true]
def Z : List Bool := [false,false]
def A (n : Nat) (R : List Bool) : Z0 := ⟨0,rep Q n ++ X,R⟩
def B (R : List Bool) : Z0 := ⟨0,Y,R⟩
def F (n : Nat) (R : List Bool) : Z0 := ⟨5,rep Q n ++ X,R⟩

theorem front (n : Nat) : [true] ++ rep Q n ++ T = rep Q n ++ X := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rep,List.append_assoc] at *
    change true::true::true::(rep Q n ++ T) = true::true::(rep Q n ++ X)
    exact congrArg (fun w => true::true::w) ih

theorem make_one (L R : List Bool) :
    run0 p 6 ⟨3,[false]++Q++L,[false]++R⟩ =
    some ⟨3,[false]++L,[false]++Z++R⟩ := by
  exact knownRun_sound p 6 (z:=⟨3,[false]++Q,[false]⟩)
    (z':=⟨3,[false],[false]++Z⟩) (by decide) L R

theorem make (n : Nat) (R : List Bool) :
    run0 p (6*n+2) (A n R) = some (B (Q++rep Z n++R)) := by
  cases n with
  | zero =>
    simpa [A,B,rep,extend] using knownRun_sound p 2 (z:=⟨0,X,[]⟩)
      (z':=⟨0,Y,Q⟩) (by decide) [] R
  | succ n =>
    have h1 : run0 p 3 (A (n+1) R) = some ⟨3,[false]++rep Q n++X,[false]++R⟩ := by
      simpa [A,rep,extend,List.append_assoc] using knownRun_sound p 3 (z:=⟨0,Q,[]⟩)
        (z':=⟨3,[false],[false]⟩) (by decide) (rep Q n++X) R
    have h2 := sweepL p 3 [false] [false] Q Z 6 make_one n X R
    have h3 : run0 p 5 ⟨3,[false]++X,[false]++rep Z n++R⟩ =
        some (B (Q++Z++rep Z n++R)) := by
      simpa [B,extend,List.append_assoc] using knownRun_sound p 5
        (z:=⟨3,[false]++X,[false]⟩) (z':=⟨0,Y,Q++Z⟩) (by decide) [] (rep Z n++R)
    simpa [rep,List.append_assoc,show 3+6*n+5=6*(n+1)+2 by omega] using join0 (join0 h1 h2) h3

theorem load_one (L R : List Bool) :
    run0 p 2 ⟨5,[true]++L,[]++Q++R⟩ = some ⟨5,[true]++Q++L,[]++R⟩ := by
  exact knownRun_sound p 2 (z:=⟨5,[true],Q⟩) (z':=⟨5,[true]++Q,[]⟩) (by decide) L R

theorem load (n : Nat) (R : List Bool) :
    run0 p (4+2*n) (B (rep Q (n+1)++R)) = some (F n R) := by
  have h1 : run0 p 4 (B (rep Q (n+1)++R)) = some ⟨5,X,rep Q n++R⟩ := by
    simpa [B,rep,extend,List.append_assoc] using knownRun_sound p 4 (z:=⟨0,Y,Q⟩)
      (z':=⟨5,X,[]⟩) (by decide) [] (rep Q n++R)
  have h2 : run0 p (2*n) ⟨5,X,rep Q n++R⟩ = some (F n R) := by
    unfold F
    rw [← front]
    exact sweepR p 5 [true] [] Q Q 2 load_one n T R
  exact join0 h1 h2

theorem carry (n : Nat) (R : List Bool) :
    run0 p (8+2*n) (B (rep Q (n+1)++Z++R)) = some (A n (Q++R)) := by
  have h1 := load n (Z++R)
  have h2 : run0 p 4 (F n (Z++R)) = some (A n (Q++R)) := by
    rw [F,A,← front]
    simpa [extend,List.append_assoc] using knownRun_sound p 4 (z:=⟨5,[true],Z⟩)
      (z':=⟨0,[true],Q⟩) (by decide) (rep Q n++T) R
  simpa [List.append_assoc,show 4+2*n+4=8+2*n by omega] using join0 h1 h2

def clearCost : Nat → Nat
  | 0 => 0
  | n+1 => clearCost n + (8+2*n) + (6*n+2) + clearCost n

theorem snoc (P : List Bool) (n : Nat) (R : List Bool) :
    rep P (n+1) ++ R = rep P n ++ (P++R) := by
  rw [← List.append_assoc,rep_snoc P n]
  rfl

/-- A binary block increments completely, leaving the right suffix untouched. -/
theorem clear (n : Nat) (R : List Bool) :
    run0 p (clearCost n) (B (Q++rep Z n++R)) = some (B (rep Q (n+1)++R)) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    rw [List.append_assoc,snoc Z n,clearCost]
    have h1 := ih (Z++R)
    have h2 := carry n R
    have h3 := make n (Q++R)
    have h4 := ih (Q++R)
    rw [snoc Q (n+1)]
    simpa only [List.append_assoc] using join0 (join0 (join0 h1 (by simpa only [List.append_assoc] using h2))
      (by simpa only [List.append_assoc] using h3)) (by simpa only [List.append_assoc] using h4)

theorem finish (n : Nat) : run0 p (8+2*n) (B (rep Q (n+1))) = some (A n Q) := by
  have h1 : run0 p (4+2*n) (B (rep Q (n+1))) = some (F n []) := by
    simpa using load n []
  have h2 : run0 p 4 (F n []) = some (A n Q) := by
    rw [F,A,← front]
    rfl
  simpa [show 4+2*n+4=8+2*n by omega] using join0 h1 h2

def cost (n : Nat) := (6*n+2)+clearCost n+(8+2*(n+1))
theorem growth (n : Nat) : run0 p (cost n) (A n Q) = some (A (n+1) Q) := by
  have h := join0 (make n Q) (clear n Q)
  have he : rep Q (n+1) ++ Q = rep Q (n+1+1) := rep_snoc Q (n+1)
  rw [he] at h
  exact join0 h (finish (n+1))

theorem first : run0 p 27 ⟨0,[],[]⟩ = some (A 0 Q) := by decide

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_growth p (fun n => A n Q) 27 cost first _ growth m hm
  intro n; unfold cost; omega

#print axioms clear
#print axioms growth
#print axioms never
end BB6.Agent46Raw13OneLC.Binary
