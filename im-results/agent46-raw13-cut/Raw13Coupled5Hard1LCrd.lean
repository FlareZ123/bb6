import SweepPumping
import FastFAR

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13Coupled5Hard1LCrd
open BB6Coverage BB6Coverage.Agent31Pump

/-- Literal residual 1RB1LD1RC1RD1LA1RE1LC0LA1RF0RD---0RA. -/
def p : PartialMachine := FAR.fromCodes [7,14,11,15,2,19,10,0,23,13,24,1]
abbrev Y : List Bool := [false,true]
abbrev U : List Bool := [true,true]
abbrev I : List Bool := [false,true,false,true,false,true,false,true]
abbrev O : List Bool := [true,true,true,true,true,true,true,true]
abbrev F5 : List Bool := [true,true,true,true,true]
abbrev F9 : List Bool := [true,true,true,true,true,true,true,true,true]

theorem commuteRep (P Q : List Bool) (h : P++Q=Q++P) (k : Nat) :
    P++rep Q k = rep Q k++P := by
  induction k with
  | zero => simp [rep]
  | succ k ih =>
    calc
      P++rep Q (k+1) = (P++Q)++rep Q k := by simp only [rep,List.append_assoc]
      _ = (Q++P)++rep Q k := by rw [h]
      _ = Q++(P++rep Q k) := List.append_assoc _ _ _
      _ = Q++(rep Q k++P) := by rw [ih]
      _ = rep Q (k+1)++P := by simp only [rep,List.append_assoc]

theorem sweepRight (L R : List Bool) :
    run0 p 28 ⟨5,F5++L,Y++I++R⟩ = some ⟨5,F5++O++L,Y++R⟩ := by rfl

theorem endRight (L : List Bool) :
    run0 p 10 ⟨5,F5++L,Y++U⟩ = some ⟨5,F9++L,[]⟩ := by rfl

theorem turn (L : List Bool) :
    run0 p 14 ⟨5,F9++L,[]⟩ = some ⟨0,F9++L,Y++U⟩ := by rfl

theorem sweepLeft (L R : List Bool) :
    run0 p 8 ⟨0,[]++O++L,[]++R⟩ = some ⟨0,[]++L,[]++I++R⟩ := by rfl

theorem finish (R : List Bool) :
    run0 p 12 ⟨0,[true],R⟩ = some ⟨5,F5,R⟩ := by rfl

def fam (k : Nat) : Z0 := ⟨5,F5,Y++rep I k++U⟩

theorem advance (k : Nat) :
    run0 p (44+36*k) (fam k) = some (fam (k+1)) := by
  have h1 : run0 p (28*k) (fam k) =
      some ⟨5,F5++rep O k,Y++U⟩ := by
    simpa only [fam,List.append_nil,List.append_assoc] using
      sweepR p 5 F5 Y I O 28 sweepRight k [] U
  have h2 := endRight (rep O k)
  have h3 := turn (rep O k)
  have h4 : run0 p (8*(k+1)) ⟨0,F9++rep O k,Y++U⟩ =
      some ⟨0,[true],rep I (k+1)++(Y++U)⟩ := by
    have w : F9++rep O k = rep O (k+1)++[true] := by
      change O++([true]++rep O k) = _
      rw [commuteRep [true] O (by rfl)]
      simp only [rep,List.append_assoc]
    rw [w]
    simpa only [List.nil_append] using sweepL p 0 [] [] O I 8 sweepLeft (k+1) [true] (Y++U)
  have h5 : run0 p 12 ⟨0,[true],rep I (k+1)++(Y++U)⟩ =
      some (fam (k+1)) := by
    have w : rep I (k+1)++(Y++U) = Y++rep I (k+1)++U := by
      rw [← List.append_assoc,← commuteRep Y I (by rfl),List.append_assoc]
    rw [w]
    exact finish (Y++rep I (k+1)++U)
  have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  simpa only [show 28*k+10+14+8*(k+1)+12=44+36*k by omega] using h

theorem seed : run0 p 25 ⟨0,[],[]⟩ = some (fam 0) := by rfl

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  never_of_growth p fam 25 (fun k => 44+36*k) seed (by intro k; omega) advance m hm

#print axioms advance
#print axioms never
end BB6.Agent46Raw13Coupled5Hard1LCrd
