import Agent46AutoPump
import FastFAR

namespace BB6.Agent46Raw13OneLC.Ternary
open BB6Coverage BB6Coverage.Agent31Pump
open BB6Coverage.Agent31Pump.Auto (knownRun knownRun_sound extend)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def p : PartialMachine := FAR.fromCodes [7,10,11,12,2,5,10,17,21,24,13,3]
def X : List Bool := [true,true,true,false,false,false,true,false,false]
def P : List Bool := [true,false]
def Q : List Bool := [true,true]
def Z : List Bool := [false,false]
def A (n : Nat) (R : List Bool) : Z0 := ⟨0,rep P n ++ X,R⟩
def B (n : Nat) (R : List Bool) : Z0 := ⟨1,Z ++ rep P n ++ X,R⟩
def D (n : Nat) (R : List Bool) : Z0 := A 0 (rep Q (n+1) ++ R)

theorem shift_one (L R : List Bool) :
    run0 p 2 ⟨0,[]++P++L,[]++R⟩ = some ⟨0,[]++L,[]++Q++R⟩ := by
  exact knownRun_sound p 2 (z:=⟨0,P,[]⟩) (z':=⟨0,[],Q⟩) (by decide) L R

theorem shift (n : Nat) (R : List Bool) :
    run0 p (2*n) (A n R) = some (A 0 (rep Q n ++ R)) := by
  simpa [A,rep] using sweepL p 0 [] [] P Q 2 shift_one n X R

theorem clear_one (R : List Bool) : run0 p 52 (D 0 R) = some (B 0 R) := by
  simpa [A,B,D,rep,extend] using knownRun_sound p 52 (z:=⟨0,X,Q⟩)
    (z':=⟨1,Z++X,[]⟩) (by decide) [] R

theorem carry_two (k : Nat) (R : List Bool) :
    run0 p (8+2*k) (B k (Q++R)) = some (D k (Z++R)) := by
  have h1 : run0 p 8 (B k (Q++R)) = some (A k (Q++Z++R)) := by
    simpa [B,A,extend,List.append_assoc] using knownRun_sound p 8 (z:=⟨1,Z,Q⟩)
      (z':=⟨0,[],Q++Z⟩) (by decide) (rep P k++X) R
  have h2 := shift k (Q++Z++R)
  have he : rep Q k ++ (Q ++ (Z ++ R)) = rep Q (k+1) ++ (Z ++ R) := by
    rw [← List.append_assoc,rep_snoc Q k]
    rfl
  simpa only [D,List.append_assoc,he] using join0 h1 h2

theorem carry_one (k : Nat) (R : List Bool) :
    run0 p (4+2*k) (B k (Z++R)) = some (D k (P++R)) := by
  have h1 : run0 p 2 (B k (Z++R)) = some (A (k+1) (P++R)) := by
    simpa [A,B,extend,rep,List.append_assoc] using knownRun_sound p 2 (z:=⟨1,Z,Z⟩)
      (z':=⟨0,P,P⟩) (by decide) (rep P k++X) R
  have h2 := shift (k+1) (P++R)
  simpa [D,show 2+2*(k+1)=4+2*k by omega] using join0 h1 h2

theorem carry_zero (k : Nat) (R : List Bool) :
    run0 p 2 (B k (P++R)) = some (B (k+1) R) := by
  simpa [B,extend,rep,List.append_assoc] using knownRun_sound p 2 (z:=⟨1,Z,P⟩)
    (z':=⟨1,Z++P,[]⟩) (by decide) (rep P k++X) R

/-- Drain an arbitrary-length ternary block with an untouched right suffix. -/
def drainCost : Nat → Nat
  | 0 => 52
  | k+1 => drainCost k + (8+2*k) + drainCost k + (4+2*k) + drainCost k + 2

theorem drain (k : Nat) (R : List Bool) : run0 p (drainCost k) (D k R) = some (B k R) := by
  induction k generalizing R with
  | zero => exact clear_one R
  | succ k ih =>
    have h0 : D (k+1) R = D k (Q++R) := by
      unfold D A
      have h : rep Q (k+1+1) = rep Q (k+1) ++ Q := (rep_snoc Q (k+1)).symm
      rw [h,List.append_assoc]
    rw [h0,drainCost]
    exact join0 (join0 (join0 (join0 (join0 (ih (Q++R)) (carry_two k R))
      (ih (Z++R))) (carry_one k R)) (ih (P++R))) (carry_zero k R)

theorem finish (k : Nat) : run0 p 4 (B k [true]) = some (A (k+2) [true]) := by
  rfl

def cost : Nat → Nat
  | 0 => 18
  | n+1 => 2*(n+1) + drainCost n + 4

theorem growth (n : Nat) : run0 p (cost n) (A n [true]) = some (A (n+1) [true]) := by
  cases n with
  | zero => decide
  | succ n =>
    have h := shift (n+1) [true]
    exact join0 (join0 h (drain n [true])) (finish n)

theorem first : run0 p 28 ⟨0,[],[]⟩ = some (A 0 [true]) := by decide

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_growth p (fun n => A n [true]) 28 cost first _ growth m hm
  intro k; cases k <;> simp [cost]

#print axioms drain
#print axioms growth
#print axioms never
end BB6.Agent46Raw13OneLC.Ternary
