import Raw54Return
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.LFCounter35
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def O : List Bool := [true,true,true]
def Z : List Bool := [false,false,false]
def L : List Bool := [false,false,true,true,false,false]
def P : List Bool := [true,false,false]
def enc : List Bool → List Bool
  | [] => [true,true]
  | b::bs => true::true::(!b)::enc bs
def cfg (bs : List Bool) : Z0 := ⟨5,[false],P ++ enc bs⟩
def scanCfg (k : Nat) (bs : List Bool) : Z0 := ⟨5,false::(rep Z k ++ L),enc bs⟩
def bump : List Bool → List Bool
  | [] => [false]
  | false::bs => true::bs
  | true::bs => false::bump bs

theorem encRep (k : Nat) (bs : List Bool) : enc (List.replicate k false ++ bs) = rep O k ++ enc bs := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ,List.cons_append,enc,ih,rep]; rfl

theorem finish (k : Nat) (R : List Bool) : run0 table (3*k+5) ⟨3,rep Z k ++ L,R⟩ = some ⟨5,[false],P ++ rep O k ++ true::true::R⟩ := by
  have a := sweepL table 3 [] [] Z O 3 (by intro L R; rfl) k L R
  have b : run0 table 5 ⟨3,L,rep O k ++ R⟩ = some ⟨5,[false],P ++ [true,true] ++ (rep O k ++ R)⟩ := by rfl
  have H := join0 a b
  have rot : ∀ k : Nat, [true,true] ++ (rep O k ++ R) = rep O k ++ true::true::R := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simp only [rep,List.append_assoc]; change true::true::true::([true,true] ++ (rep O k ++ R)) = true::true::true::(rep O k ++ true::true::R); rw [ih]
  simp only [List.nil_append,List.append_assoc] at H ⊢
  rw [rot] at H
  exact H

theorem reset (k : Nat) (bs : List Bool) : ∃ t,0<t ∧ run0 table t ⟨5,true::(rep Z k ++ L),enc bs⟩ = some (cfg (List.replicate k false ++ true::bs)) := by
  have a : run0 table 1 ⟨5,true::(rep Z k ++ L),enc bs⟩ = some ⟨3,rep Z k ++ L,false::enc bs⟩ := by rfl
  have H := join0 a (finish k (false::enc bs))
  refine ⟨1+(3*k+5),by omega,?_⟩
  unfold cfg
  rw [encRep]
  simpa [enc,List.append_assoc] using H

theorem scan (bs : List Bool) (k : Nat) : ∃ t,0<t ∧ run0 table t (scanCfg k bs) = some (cfg (List.replicate (k+1) false ++ bump bs)) := by
  induction bs generalizing k with
  | nil =>
    have a : run0 table 5 (scanCfg k []) = some ⟨3,rep Z (k+2) ++ L,[]⟩ := by rfl
    have H := join0 a (finish (k+2) [])
    refine ⟨5+(3*(k+2)+5),by omega,?_⟩
    unfold cfg
    rw [show List.replicate (k+1) false ++ bump [] = List.replicate (k+2) false ++ [] by simp only [bump,List.append_nil]; rw [← List.replicate_succ']]
    rw [encRep]
    simpa [enc,List.append_assoc] using H
  | cons b bs ih =>
    cases b
    · have a : run0 table 3 (scanCfg k (false::bs)) = some ⟨5,true::(rep Z (k+1) ++ L),enc bs⟩ := by rfl
      obtain ⟨t,ht,h⟩ := reset (k+1) bs
      exact ⟨3+t,by omega,join0 a h⟩
    · have a : run0 table 3 (scanCfg k (true::bs)) = some (scanCfg (k+1) bs) := by rfl
      obtain ⟨t,ht,h⟩ := ih (k+1)
      have H := join0 a h
      refine ⟨3+t,by omega,?_⟩
      rw [List.replicate_succ',List.append_assoc] at H
      exact H

theorem epoch (bs : List Bool) : ∃ t,0<t ∧ run0 table t (cfg bs) = some (cfg (bump bs)) := by
  cases bs with
  | nil =>
    have a : run0 table 8 (cfg []) = some ⟨3,rep Z 1 ++ L,[]⟩ := by rfl
    have H := join0 a (finish 1 [])
    exact ⟨8+(3*1+5),by omega,H⟩
  | cons b bs =>
    cases b
    · have a : run0 table 6 (cfg (false::bs)) = some ⟨5,true::L,enc bs⟩ := by rfl
      obtain ⟨t,ht,h⟩ := reset 0 bs
      exact ⟨6+t,by omega,join0 a h⟩
    · have a : run0 table 6 (cfg (true::bs)) = some (scanCfg 0 bs) := by rfl
      obtain ⟨t,ht,h⟩ := scan bs 0
      exact ⟨6+t,by omega,join0 a h⟩
def orbit : Nat → List Bool | 0 => [false] | n+1 => bump (orbit n)
def family (n : Nat) := cfg (orbit n)
theorem first : run0 table 24 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem next (n : Nat) : ∃ t,0<t ∧ run0 table t (family n) = some (family (n+1)) := epoch (orbit n)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent8Raw54.never_of_returns table family 24 first next m hm
#print axioms never
end BB6.Agent8Raw54.LFCounter35
