import Raw54Return
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.LFCounter37
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨true,true,5⟩)
  | _,_ => none

def O : List Bool := [true,true,true]
def Z : List Bool := [false,false,false]
def enc : List Bool → List Bool
  | [] => O
  | b::bs => b::b::b::enc bs
def P : List Bool := [true,false,false]
def L : List Bool := [true,true,true,true,false,false]
def cfg (b : Bool) (bs : List Bool) : Z0 := ⟨5,[false],P ++ b::b::enc bs⟩
def scanCfg (k : Nat) (bs : List Bool) : Z0 := ⟨5,true::(rep O k ++ [true,true,true,false,false]),enc bs⟩
def bump : List Bool → List Bool
  | [] => [false]
  | false::bs => true::bs
  | true::bs => false::bump bs

theorem encRep (k : Nat) (bs : List Bool) : enc (List.replicate k false ++ bs) = rep Z k ++ enc bs := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ,List.cons_append,enc,ih,rep]; rfl

theorem finish (k : Nat) (R : List Bool) : run0 table (11+3*k) ⟨5,true::(rep O k ++ [true,true,true,false,false]),false::false::false::R⟩ = some ⟨5,[false],P ++ [false,false] ++ (rep Z k ++ O ++ R)⟩ := by
  have a : run0 table 7 ⟨5,true::(rep O k ++ [true,true,true,false,false]),false::false::false::R⟩ = some ⟨4,rep O k ++ [true,true,true,false,false],false::O++R⟩ := by rfl
  have b := sweepL table 4 [] [] O Z 3 (by intro L R; rfl) k [true,true,true,false,false] (false::O++R)
  have c : run0 table 4 ⟨4,[true,true,true,false,false],rep Z k ++ (false::O++R)⟩ = some ⟨5,[false],P ++ [false,false] ++ (rep Z k ++ O ++ R)⟩ := by
    have rot : rep Z k ++ (false::O++R) = false::(rep Z k ++ O++R) := by
      clear a b
      induction k with
      | zero => rfl
      | succ k ih => simp only [rep,List.append_assoc,Z,List.cons_append,List.nil_append] at ih ⊢; rw [ih]
    rw [rot]; rfl
  have H := join0 (join0 a b) c
  rw [show 11+3*k=7+3*k+4 by omega]
  exact H

theorem scan (bs : List Bool) (k : Nat) : ∃ t,0<t ∧ run0 table t (scanCfg k bs) = some (cfg false (List.replicate k false ++ bump bs)) := by
  induction bs generalizing k with
  | nil =>
    have a : run0 table 3 (scanCfg k []) = some ⟨5,true::(rep O (k+1) ++ [true,true,true,false,false]),[]⟩ := by rfl
    have b : run0 table (11+3*(k+1)) ⟨5,true::(rep O (k+1) ++ [true,true,true,false,false]),[]⟩ = some ⟨5,[false],P ++ [false,false] ++ (rep Z (k+1) ++ O)⟩ := by
      have c : run0 table 7 ⟨5,true::(rep O (k+1) ++ [true,true,true,false,false]),[]⟩ = some ⟨4,rep O (k+1) ++ [true,true,true,false,false],false::O⟩ := by rfl
      have H := sweepL table 4 [] [] O Z 3 (by intro L R; rfl) (k+1) [true,true,true,false,false] (false::O)
      have e : run0 table 4 ⟨4,[true,true,true,false,false],rep Z (k+1) ++ false::O⟩ = some ⟨5,[false],P ++ [false,false] ++ (rep Z (k+1) ++ O)⟩ := by
        have rot : ∀ n : Nat, rep Z n ++ false::O = false::(rep Z n ++ O) := by
          intro n; induction n with
          | zero => rfl
          | succ n ih => simp only [rep,List.append_assoc]; change false::false::false::(rep Z n ++ false::O) = false::false::false::false::(rep Z n ++ O); rw [ih]
        rw [rot]; rfl
      have J := join0 (join0 c H) e
      rw [show 11+3*(k+1)=7+3*(k+1)+4 by omega]
      exact J
    refine ⟨3+(11+3*(k+1)),by omega,?_⟩
    have H := join0 a b
    unfold cfg
    rw [show List.replicate k false ++ bump [] = List.replicate (k+1) false ++ [] by simp only [bump,List.append_nil]; rw [← List.replicate_succ'],encRep]
    simpa [enc,List.append_assoc] using H
  | cons b bs ih =>
    cases b
    · have H := finish k (enc bs)
      refine ⟨11+3*k,by omega,?_⟩
      unfold cfg
      rw [encRep]
      simpa [scanCfg,bump,enc,O,List.append_assoc] using H
    · have a : run0 table 3 (scanCfg k (true::bs)) = some (scanCfg (k+1) bs) := by rfl
      obtain ⟨t,ht,h⟩ := ih (k+1)
      have H := join0 a h
      refine ⟨3+t,by omega,?_⟩
      rw [List.replicate_succ',List.append_assoc] at H
      exact H

def orbit : Nat → Bool × List Bool
  | 0 => (false,[])
  | n+1 => let (b,bs) := orbit n; if b then (false,bump bs) else (true,bs)
def family (n : Nat) := cfg (orbit n).1 (orbit n).2
theorem first : run0 table 28 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem next (n : Nat) : ∃ t,0<t ∧ run0 table t (family n) = some (family (n+1)) := by
  unfold family
  cases h : orbit n with
  | mk b bs =>
    cases b
    · exact ⟨10,by omega,by simp only [orbit,h,Bool.false_eq_true,ite_false]; rfl⟩
    · have a : run0 table 9 (cfg true bs) = some (scanCfg 0 bs) := by rfl
      obtain ⟨t,ht,hb⟩ := scan bs 0
      exact ⟨9+t,by omega,by simpa [orbit,h] using join0 a hb⟩
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent8Raw54.never_of_returns table family 28 first next m hm
#print axioms never
end BB6.Agent8Raw54.LFCounter37
