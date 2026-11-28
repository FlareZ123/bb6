import Box27SliceCore
import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent49.Box27D14V18Alternating
open BB6Coverage BB6.Agent13BlankDelay BB6Coverage.Agent31Pump
open BB6.Agent13.Box17 (decode index)

def p : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,false,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,_ => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨false,true,3⟩)
  | 3,true => some (some ⟨false,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def P : List Bool := [false,true,false,true]
def Q : List Bool := [true,false,true,false]
def cap : List Bool := [true,false,true]
def family (k : Nat) : Z0 := ⟨0,[],rep Q (k+1)⟩

theorem first : run0 p 14 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem prelude (R : List Bool) : run0 p 4 ⟨0,[],Q++R⟩ = some ⟨0,[false]++P,R⟩ := by rfl

theorem rightAtom (L R : List Bool) :
    run0 p 4 ⟨0,[false]++L,[]++Q++R⟩ = some ⟨0,[false]++P++L,[]++R⟩ := by rfl

theorem turn (L : List Bool) : run0 p 10 ⟨0,[false,false]++L,[]⟩ = some ⟨0,cap++[false]++L,[]⟩ := by rfl

theorem leftAtom (L R : List Bool) :
    run0 p 4 ⟨0,[]++Q++L,[]++R⟩ = some ⟨0,[]++L,[]++Q++R⟩ := by rfl

theorem finish (R : List Bool) : run0 p 4 ⟨0,cap,R⟩ = some ⟨0,[],Q++R⟩ := by rfl

theorem rotateCap (n : Nat) : cap ++ rep P n = rep Q n ++ cap := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep,rep,← List.append_assoc,show cap++P=Q++cap by rfl,List.append_assoc,ih,List.append_assoc]

theorem growth (k : Nat) : run0 p (22+8*k) (family k) = some (family (k+1)) := by
  have h1 := prelude (rep Q k)
  have h2 := sweepR p 0 [false] [] Q P 4 rightAtom k P []
  simp only [List.nil_append,List.append_nil] at h2
  have h2' : run0 p (4*k) ⟨0,[false]++P,rep Q k⟩ = some ⟨0,[false]++rep P (k+1),[]⟩ := by
    simpa only [rep,List.append_assoc,rep_snoc P k] using h2
  have h3a : run0 p 10 ⟨0,[false]++rep P (k+1),[]⟩ = some ⟨0,cap++rep P (k+1),[]⟩ := by
    simpa only [rep,P,List.cons_append,List.nil_append,List.append_assoc] using turn ([true,false,true]++rep P k)
  rw [rotateCap] at h3a
  have h4 := sweepL p 0 [] [] Q Q 4 leftAtom (k+1) cap []
  simp only [List.nil_append,List.append_nil] at h4
  have h5 := finish (rep Q (k+1))
  have H := join0 (join0 (join0 (join0 h1 h2') h3a) h4) h5
  simpa only [family,rep,show 4+4*k+10+4*(k+1)+4=22+8*k by omega] using H

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  never_of_growth p family 14 (fun k => 22+8*k) first (by intro k; omega) growth m hm

theorem bound (B : Nat) : BB6.Agent49.Box27Slice.Good B p := by
  intro m hm
  exact weighted_of_never B m (never m hm)

#print axioms growth
#print axioms never
#print axioms bound
end BB6.Agent49.Box27D14V18Alternating
