import FastFAR
import SweepPumping
import WeightedTNF
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent6C1ZeroLAFour
open BB6Coverage BB6Coverage.Agent31Pump

inductive V | a | b | c | d
open V
def ctr : V → PartialMachine
  | a => FAR.fromCodes [7,4,11,23,14,0,3,16,12,11,13,24]
  | b => FAR.fromCodes [7,6,11,23,14,0,3,16,12,11,24,13]
  | c => FAR.fromCodes [7,20,11,24,14,0,3,16,12,11,13,23]
  | d => FAR.fromCodes [7,13,11,24,14,0,3,16,12,11,24,24]
def scanCost : V → Nat | d => 5 | _ => 7
def startCost : V → Nat | d => 9 | _ => 11
def bCost : V → Nat | d => 15 | _ => 19
def entryCost : V → Nat | d => 30 | _ => 34
abbrev P : List Bool := [false,true,true]
abbrev Q : List Bool := [true,false,false]
abbrev T : List Bool := [false,false,true]
abbrev L0 : List Bool := [false,false,true,true]
abbrev h : List Bool := [true]
abbrev f : List Bool := [false]
def z (n : Nat) := List.replicate n false
def u (n : Nat) := List.replicate n true
def as (n : Nat) := rep P n
def bs (n : Nat) := rep Q n
def cs (n : Nat) := rep T n

theorem start (v : V) (R : List Bool) : run0 (ctr v) (startCost v) ⟨4,h,f++R⟩ = some ⟨3,L0,R⟩ := by cases v <;> rfl
theorem scan (v : V) (L R : List Bool) : run0 (ctr v) (scanCost v) ⟨3,L0++L,T++R⟩ = some ⟨3,L0++P++L,R⟩ := by cases v <;> rfl
theorem turnA (v : V) (L R : List Bool) : run0 (ctr v) 11 ⟨3,L0++L,z 3++R⟩ = some ⟨4,P++L,f++u 3++R⟩ := by cases v <;> rfl
theorem turnB (v : V) (L R : List Bool) : run0 (ctr v) (bCost v) ⟨3,L0++L,z 2++u 3++R⟩ = some ⟨4,P++L,f++h++z 4++R⟩ := by cases v <;> rfl
theorem pop (v : V) (L R : List Bool) : run0 (ctr v) 5 ⟨4,P++L,f++R⟩ = some ⟨4,L,f++Q++R⟩ := by cases v <;> rfl
theorem finish (v : V) (R : List Bool) : run0 (ctr v) 2 ⟨4,P,f++R⟩ = some ⟨4,h,z 3++R⟩ := by cases v <;> rfl

theorem rep_add (P : List Bool) (a b : Nat) : rep P (a+b) = rep P a ++ rep P b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [show a+1+b=a+b+1 by omega]; change P ++ rep P (a+b) = (P ++ rep P a) ++ rep P b; rw [ih,List.append_assoc]
theorem z_add (a b : Nat) : z (a+b) = z a ++ z b := by
  induction a with
  | zero => simp [z]
  | succ a ih => rw [show a+1+b=a+b+1 by omega]; change false :: z (a+b) = false :: (z a ++ z b); rw [ih]
theorem shift (n : Nat) : z 2++bs n = cs n++z 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change z 2 ++ (Q ++ bs n) = (T ++ cs n) ++ z 2
    have H : z 2++Q=T++z 2 := rfl
    rw [←List.append_assoc,H,List.append_assoc,ih,List.append_assoc]

theorem sweep (v : V) (n : Nat) (L R : List Bool) :
    run0 (ctr v) (scanCost v*n) ⟨3,L0++L,cs n++R⟩ = some ⟨3,L0++as n++L,R⟩ := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have H := join0 (scan v L (cs n++R)) (ih (P++L))
    have hc : scanCost v+scanCost v*n=scanCost v*(n+1) := by rw [Nat.mul_succ,Nat.add_comm]
    rw [hc] at H
    have hp : as (n+1)=as n++P := by change rep P (n+1)=rep P n++rep P 1; rw [rep_add]
    rw [hp]
    simpa only [cs,rep,List.append_assoc] using H

theorem unwind (v : V) (n : Nat) (L R : List Bool) :
    run0 (ctr v) (5*n) ⟨4,as n++L,f++R⟩ = some ⟨4,L,f++bs n++R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have H := join0 (pop v (as n++L) R) (ih (Q++R))
    rw [show 5+5*n=5*(n+1) by omega] at H
    have hq : bs (n+1)=bs n++Q := by change rep Q (n+1)=rep Q n++rep Q 1; rw [rep_add]
    rw [hq]
    simpa only [as,rep,List.append_assoc] using H

def A (n : Nat) : Z0 := ⟨4,h,z 3++bs n++z (n+2)++u 3⟩
def B (n : Nat) : Z0 := ⟨4,h,z 3++bs n++u 3++z (n+1)++u 3⟩
def costA (v : V) (n : Nat) := startCost v + scanCost v*n + 11 + 5*n + 2
def costB (v : V) (n : Nat) := startCost v + scanCost v*n + bCost v + 5*n + 2

theorem phaseA (v : V) (n : Nat) : run0 (ctr v) (costA v n) (A n) = some (B n) := by
  have H1 := start v (z 2++bs n++z (n+2)++u 3)
  have H2 := sweep v n [] (z 3++z (n+1)++u 3)
  have H3 := turnA v (as n) (z (n+1)++u 3)
  have H4 := unwind v n P (u 3++z (n+1)++u 3)
  have H5 := finish v (bs n++u 3++z (n+1)++u 3)
  have hshift : z 2++bs n++z (n+2)++u 3 = cs n++(z 3++z (n+1)++u 3) := by
    have he : z 2++z (n+2)=z 3++z (n+1) := by rw [←z_add,←z_add]; congr 1; omega
    rw [shift]
    simp only [List.append_assoc]
    rw [←List.append_assoc (z 2),he]
    simp only [List.append_assoc]
  rw [hshift] at H1
  have H := join0 H1 (by simpa only [List.append_nil] using H2)
  have hp : as n++P=P++as n := by change rep P n++rep P 1=rep P 1++rep P n; rw [←rep_add,←rep_add,Nat.add_comm]
  rw [←hp] at H3
  have H := join0 H (by simpa only [List.append_assoc] using H3)
  have H := join0 H (by simpa only [List.append_assoc] using H4)
  have H := join0 H (by simpa only [List.append_assoc] using H5)
  unfold costA A B
  have he : z 3++bs n++z (n+2)++u 3 = f++(cs n++(z 3++z (n+1)++u 3)) := by
    calc
      z 3++bs n++z (n+2)++u 3 = f++(z 2++bs n++z (n+2)++u 3) := by simp only [←List.append_assoc]; rfl
      _ = _ := congrArg (fun X => f++X) hshift
  rw [he]
  simpa only [List.append_assoc] using H

theorem phaseB (v : V) (n : Nat) : run0 (ctr v) (costB v n) (B n) = some (A (n+1)) := by
  have H1 := start v (z 2++bs n++u 3++z (n+1)++u 3)
  have H2 := sweep v n [] (z 2++u 3++z (n+1)++u 3)
  have H3 := turnB v (as n) (z (n+1)++u 3)
  have H4 := unwind v n P (h++z 4++z (n+1)++u 3)
  have H5 := finish v (bs n++h++z 4++z (n+1)++u 3)
  rw [shift] at H1
  have H := join0 H1 (by simpa only [List.append_assoc,List.append_nil] using H2)
  have hp : as n++P=P++as n := by change rep P n++rep P 1=rep P 1++rep P n; rw [←rep_add,←rep_add,Nat.add_comm]
  rw [←hp] at H3
  have H := join0 H (by simpa only [List.append_assoc] using H3)
  have H := join0 H (by simpa only [List.append_assoc] using H4)
  have H := join0 H (by simpa only [List.append_assoc] using H5)
  have hq : bs (n+1)=bs n++Q := by change rep Q (n+1)=rep Q n++rep Q 1; rw [rep_add]
  have hz : h++z 4++z (n+1)=Q++z (n+3) := by
    rw [List.append_assoc h,←z_add,show 4+(n+1)=2+(n+3) by omega,z_add,←List.append_assoc]
    rfl
  unfold costB A B
  have he : z 3++bs n++u 3++z (n+1)++u 3 = f++(cs n++z 2++u 3++z (n+1)++u 3) := by
    rw [show z 3=f++z 2 by rfl]
    simp only [List.append_assoc]
    rw [←List.append_assoc (z 2),shift]
    simp only [List.append_assoc]
  rw [he,hq,show n+1+2=n+3 by omega]
  simp only [List.append_assoc] at H ⊢
  rw [←List.append_assoc (z 4) (z (n+1)),←List.append_assoc h,←List.append_assoc h,hz] at H
  simpa only [List.append_assoc] using H

theorem entry (v : V) : run0 (ctr v) (entryCost v) ⟨0,[],[]⟩ = some (A 0) := by cases v <;> rfl

theorem growth (v : V) (n : Nat) : run0 (ctr v) (costA v n+costB v n) (A n) = some (A (n+1)) := join0 (phaseA v n) (phaseB v n)
open BB6.Agent13BlankDelay
theorem never (v : V) (m : Machine) (hm : compatible (ctr v) m) : NeverHalts m :=
  never_of_growth (ctr v) A (entryCost v) (fun n => costA v n+costB v n) (entry v)
    (fun n => by unfold costA costB; omega) (growth v) m hm
theorem cover (v : V) (B : Nat) : Cover (WeightedBound B) (ctr v) :=
  .leaf _ (fun m hm => weighted_never B m (never v m hm))
#print axioms growth
#print axioms entry
#print axioms never
#print axioms cover
end BB6.Agent6C1ZeroLAFour
