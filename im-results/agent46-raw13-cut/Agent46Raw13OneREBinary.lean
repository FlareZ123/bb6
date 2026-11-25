import Agent46AutoPump
import FastFAR
namespace BB6.Agent46Raw13OneRE.Binary
open BB6Coverage BB6Coverage.Agent31Pump
open BB6Coverage.Agent31Pump.Auto (knownRun knownRun_sound extend)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def p : PartialMachine := FAR.fromCodes [7,10,11,12,2,5,19,21,23,24,8,13]
def Q : List Bool := [true,true,true,true]
def Z : List Bool := [false,false,false,false]
def X : List Bool := [true,false,true,false]
def A (n : Nat) (R : List Bool) : Z0 := ⟨0,X++rep Z n++[true,true],true::R⟩
def D (n : Nat) (R : List Bool) : Z0 := ⟨0,[true,true],[true]++rep Q n++R⟩
def F (n : Nat) (R : List Bool) : Z0 := ⟨5,[true]++rep Z n++[true,true],R⟩

theorem sweep_make (L R : List Bool) :
    run0 p 20 ⟨0,[]++Z++L,[true]++R⟩ = some ⟨0,[]++L,[true]++Z++R⟩ :=
  knownRun_sound p 20 (z:=⟨0,Z,[true]⟩) (z':=⟨0,[],[true]++Z⟩) (by decide) L R

theorem make (n : Nat) (R : List Bool) :
    run0 p (4+20*n) (A n R) = some (D 0 (rep Z n++Q++R)) := by
  have h1 : run0 p 4 (A n R) = some ⟨0,rep Z n++[true,true],[true]++Q++R⟩ := by
    simpa [A,extend,Q,List.append_assoc] using knownRun_sound p 4
      (z:=⟨0,X,[]⟩) (z':=⟨0,[],Q⟩) (by decide) (rep Z n++[true,true]) (true::R)
  have h2 := sweepL p 0 [] [true] Z Z 20 sweep_make n [true,true] (Q++R)
  simpa [D,rep,List.append_assoc] using join0 h1 h2

theorem sweep_load (L R : List Bool) :
    run0 p 4 ⟨5,[true]++L,[]++Q++R⟩ = some ⟨5,[true]++Z++L,[]++R⟩ :=
  knownRun_sound p 4 (z:=⟨5,[true],Q⟩) (z':=⟨5,[true]++Z,[]⟩) (by decide) L R

theorem load (n : Nat) (R : List Bool) :
    run0 p (5+4*n) (D n R) = some (F n R) := by
  have h1 : run0 p 5 (D n R) = some ⟨5,[true,true,true],rep Q n++R⟩ := by
    simpa [D,extend,List.append_assoc] using knownRun_sound p 5
      (z:=⟨0,[true,true],[true]⟩) (z':=⟨5,[true,true,true],[]⟩) (by decide) [] (rep Q n++R)
  have h2 := sweepR p 5 [true] [] Q Z 4 sweep_load n [true,true] R
  exact join0 h1 h2

theorem carry (n : Nat) (R : List Bool) :
    run0 p (12+4*n) (D n (Z++R)) = some (A n R) := by
  have h1 := load n (Z++R)
  have h2 : run0 p 7 (F n (Z++R)) = some (A n R) := by
    simpa [A,F,extend,List.append_assoc] using knownRun_sound p 7
      (z:=⟨5,[true],Z⟩) (z':=⟨0,X,[true]⟩) (by decide) (rep Z n++[true,true]) R
  simpa [show 5+4*n+7=12+4*n by omega] using join0 h1 h2

def clearCost : Nat → Nat
  | 0 => 0
  | n+1 => clearCost n + (12+4*n) + (4+20*n) + clearCost n

theorem snoc (P : List Bool) (n : Nat) (R : List Bool) : rep P (n+1) ++ R = rep P n ++ (P++R) := by
  rw [← List.append_assoc,rep_snoc P n]
  rfl

theorem clear (n : Nat) (R : List Bool) :
    run0 p (clearCost n) (D 0 (rep Z n++R)) = some (D n R) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    rw [snoc Z n,clearCost]
    have h1 := ih (Z++R)
    have h2 := carry n R
    have h3 := make n R
    have h4 := ih (Q++R)
    have he : D n (Q++R) = D (n+1) R := by
      unfold D
      simp only [List.append_assoc,snoc Q n]
    rw [he] at h4
    simpa only [List.append_assoc] using join0 (join0 (join0 h1 h2)
      (by simpa only [List.append_assoc] using h3)) h4

theorem finish (n : Nat) : run0 p (12+4*n) (D n []) = some (A n []) := by
  have h1 := load n []
  have h2 : run0 p 7 (F n []) = some (A n []) := by rfl
  simpa [show 5+4*n+7=12+4*n by omega] using join0 h1 h2

def cost (n : Nat) := (4+20*n)+clearCost n+(12+4*(n+1))
theorem growth (n : Nat) : run0 p (cost n) (A n []) = some (A (n+1) []) := by
  have hc := clear n (Q++[])
  have h := join0 (make n []) (by simpa only [List.append_assoc] using hc)
  have he : D n (Q++[]) = D (n+1) [] := by
    unfold D
    simp only [List.append_assoc,snoc Q n]
  rw [he] at h
  exact join0 h (finish (n+1))

theorem first : run0 p 35 ⟨0,[],[]⟩ = some (A 1 []) := by decide

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_growth p (fun n => A (n+1) []) 35 (fun n => cost (n+1)) first _ _ m hm
  · intro n; unfold cost; omega
  · intro n; exact growth (n+1)

#print axioms clear
#print axioms growth
#print axioms never
end BB6.Agent46Raw13OneRE.Binary
