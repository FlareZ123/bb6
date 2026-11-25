import Raw41CounterFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw41.F0Counter
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent47Raw41.CounterFamily
-- 1RB0LC_1RC0LE_0RD1RA_1LD1RA_0LF1LE_0RC---
def table : PartialMachine := fun s => match s.1.val,s.2 with
 | 0,false => some (some ⟨true,true,1⟩)
 | 0,true => some (some ⟨false,false,2⟩)
 | 1,false => some (some ⟨true,true,2⟩)
 | 1,true => some (some ⟨false,false,4⟩)
 | 2,false => some (some ⟨false,true,3⟩)
 | 2,true => some (some ⟨true,true,0⟩)
 | 3,false => some (some ⟨true,false,3⟩)
 | 3,true => some (some ⟨true,true,0⟩)
 | 4,false => some (some ⟨false,false,5⟩)
 | 4,true => some (some ⟨true,false,4⟩)
 | 5,false => some (some ⟨false,true,2⟩)
 | _,_ => none

inductive Digits : List Bool → Prop
 | terminal (b : Bool) : Digits [b,true,false]
 | cons (b : Bool) (R : List Bool) : Digits R → Digits (b::true::true::R)

theorem prefixOnes (n : Nat) (R : List Bool) (h : Digits R) : Digits (ones (3*n) ++ R) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [show 3*(n+1)=3*n+3 by omega]
    exact Digits.cons true _ ih

def fcfg (R : List Bool) : Z0 := ⟨5,[false],false::true::true::R⟩
def acfg (k : Nat) (R : List Bool) : Z0 := ⟨0,ones k ++ [false,false],R⟩

def Inv (z : Z0) : Prop := (∃ R, Digits R ∧ z = fcfg R) ∨ (∃ n R, Digits R ∧ z = acfg (3*n+2) R)

theorem fStart (R : List Bool) : run0 table 3 (fcfg R) = some (acfg 2 R) := by rfl

theorem aCarry (k : Nat) (R : List Bool) :
    run0 table 5 (acfg (k+2) (false::true::true::R)) = some (acfg (k+5) R) := by rfl

theorem aOne (k : Nat) (R : List Bool) :
    run0 table 4 (acfg (k+2) (true::R)) = some ⟨4,ones (k+2) ++ [false,false],false::R⟩ := by rfl

theorem aEnd (k : Nat) :
    run0 table 15 (acfg (k+2) [false,true,false]) = some ⟨4,ones (k+7) ++ [false,false],[false]⟩ := by rfl

theorem eStep (L R : List Bool) : run0 table 1 ⟨4,true::L,R⟩ = some ⟨4,L,true::R⟩ := by rfl

theorem eFill (k : Nat) (R : List Bool) :
    run0 table k ⟨4,ones k ++ [false,false],R⟩ = some ⟨4,[false,false],ones k ++ R⟩ := by
  simpa only [List.nil_append, Nat.one_mul, rep_singleton] using
    sweepL table 4 [] [] [true] [true] 1 eStep k [false,false] R

theorem eEnd (R : List Bool) : run0 table 1 ⟨4,[false,false],R⟩ = some ⟨5,[false],false::R⟩ := by rfl

theorem oneReturn (k : Nat) (R : List Bool) :
    run0 table (4+(k+2)+1) (acfg (k+2) (true::R)) = some (fcfg (ones k ++ false::R)) := by
  exact join0 (join0 (aOne k R) (eFill (k+2) (false::R))) (eEnd (ones (k+2) ++ false::R))

theorem endReturn (k : Nat) :
    run0 table (15+(k+7)+1) (acfg (k+2) [false,true,false]) = some (fcfg (ones (k+5) ++ [false])) := by
  exact join0 (join0 (aEnd k) (eFill (k+7) [false])) (eEnd (ones (k+7) ++ [false]))

theorem progress (z : Z0) (hz : Inv z) : ∃ t z', 0 < t ∧ run0 table t z = some z' ∧ Inv z' := by
  rcases hz with ⟨R,hR,rfl⟩|⟨n,R,hR,rfl⟩
  · exact ⟨3,_,by decide,fStart R,Or.inr ⟨0,R,hR,rfl⟩⟩
  cases hR with
  | terminal b =>
    cases b with
    | false =>
      refine ⟨_,_,by omega,endReturn (3*n),Or.inl ⟨_,?_,rfl⟩⟩
      rw [show 3*n+5 = 3*(n+1)+2 by omega]
      change Digits (List.replicate (3*(n+1)+2) true ++ [false])
      rw [← List.replicate_append_replicate]
      rw [List.append_assoc]
      exact prefixOnes (n+1) [true,true,false] (Digits.terminal true)
    | true => exact ⟨_,_,by omega,oneReturn (3*n) [true,false],Or.inl ⟨_,prefixOnes n _ (Digits.terminal false),rfl⟩⟩
  | cons b R h =>
    cases b with
    | false =>
      refine ⟨5,_,by decide,aCarry (3*n) R,Or.inr ⟨n+1,R,h,?_⟩⟩
      rw [show 3*n+5=3*(n+1)+2 by omega]
    | true => exact ⟨_,_,by omega,oneReturn (3*n) (true::true::R),Or.inl ⟨_,prefixOnes n _ (Digits.cons false R h),rfl⟩⟩

theorem entry : run0 table 44 ⟨0,[],[]⟩ = some (fcfg [true,true,false]) := by rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_returns table Inv 44 _ entry (Or.inl ⟨_,Digits.terminal true,rfl⟩) progress m hm
#print axioms never
end BB6.Agent47Raw41.F0Counter
