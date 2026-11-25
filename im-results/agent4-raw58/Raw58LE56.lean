import SweepPumping
import Raw58Live
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent4LE56
open BB6Coverage Agent31Pump
-- 1RB0LE_1RC---_0RD0RF_1LD1RE_0RF0RA_0RC0LD
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def D (k : Nat) (R : List Bool) : Z0 := ⟨3,rep [false,false] k ++ [false,false,true,true],R⟩
def F (k : Nat) (R : List Bool) : Z0 := ⟨5,rep [false,false] k ++ [false,false,true,true],R⟩

theorem oneComm (k : Nat) (r : List Bool) : true::(rep [true,true] k ++ r) = rep [true,true] k ++ true::r := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [rep,List.cons_append,List.nil_append,List.cons.injEq,true_and] using ih

theorem zeroComm (k : Nat) (r : List Bool) : false::(rep [false,false] k ++ r) = rep [false,false] k ++ false::r := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [rep,List.cons_append,List.nil_append,List.cons.injEq,true_and] using ih

theorem fill (k : Nat) (R : List Bool) : run0 table (2*k+6) (D k R) = some (F 0 (rep [true,true] k ++ R)) := by
  have h1 : run0 table (2*k) (D k R) = some ⟨3,[false,false,true,true],rep [true,true] k ++ R⟩ := by
    simpa only [D,List.nil_append] using sweepL table 3 [] [] [false,false] [true,true] 2
      (by intro L R; rfl) k [false,false,true,true] R
  have h2 : run0 table 6 ⟨3,[false,false,true,true],rep [true,true] k ++ R⟩ = some (F 0 (rep [true,true] k ++ R)) := by rfl
  exact join0 h1 h2

theorem scan (k : Nat) (R : List Bool) : ∃ t, run0 table t (F 0 (rep [true,true] k ++ R)) = some (F k R) := by
  induction k generalizing R with
  | zero => exact ⟨0,rfl⟩
  | succ k ih =>
    obtain ⟨a,ha⟩ := ih (true::true::R)
    have hstart : F 0 (rep [true,true] (k+1) ++ R) = F 0 (rep [true,true] k ++ true::true::R) := by
      apply congrArg (F 0)
      change rep [true,true] (k+1) ++ R = rep [true,true] k ++ ([true,true] ++ R)
      rw [← List.append_assoc,rep_snoc]; rfl
    have h1 : run0 table 3 (F k (true::true::R)) = some ⟨3,false::(rep [false,false] k ++ [false,false,true,true]),false::R⟩ := by
      cases k <;> rfl
    have h2 : run0 table (2*k) ⟨3,false::(rep [false,false] k ++ [false,false,true,true]),false::R⟩ =
      some ⟨3,[false,false,false,true,true],rep [true,true] k ++ false::R⟩ := by
      rw [zeroComm]
      simpa only [List.nil_append] using sweepL table 3 [] [] [false,false] [true,true] 2
        (by intro L R; rfl) k [false,false,false,true,true] (false::R)
    have h3 : run0 table 7 ⟨3,[false,false,false,true,true],rep [true,true] k ++ false::R⟩ = some (F 0 (rep [true,true] k ++ true::false::R)) := by
      have H : run0 table 7 ⟨3,[false,false,false,true,true],rep [true,true] k ++ false::R⟩ = some (F 0 (true::(rep [true,true] k ++ false::R))) := by rfl
      rw [oneComm] at H
      exact H
    obtain ⟨b,hb⟩ := ih (true::false::R)
    have h4 : run0 table 2 (F k (true::false::R)) = some (F (k+1) R) := by
      cases k <;> rfl
    rw [hstart]
    exact ⟨_,join0 (join0 (join0 (join0 (join0 ha h1) h2) h3) hb) h4⟩

theorem grow (k : Nat) : ∃ t, 0 < t ∧ run0 table t (D k []) = some (D (k+1) []) := by
  have h1 := fill k []
  obtain ⟨t,h2⟩ := scan k []
  have h3 : run0 table 2 (F k []) = some (D (k+1) []) := by cases k <;> rfl
  exact ⟨_,by omega,join0 (join0 h1 h2) h3⟩

theorem arbitrary (n : Nat) : ∃ t z, n ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some z := by
  have aux : ∀ n : Nat, ∃ t, n ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some (D n []) := by
    intro n
    induction n with
    | zero => exact ⟨3,by omega,by rfl⟩
    | succ n ih =>
      obtain ⟨t,ht,hh⟩ := ih
      obtain ⟨u,hu,hr⟩ := grow n
      exact ⟨t+u,by omega,join0 hh hr⟩
  obtain ⟨t,ht,hh⟩ := aux n
  exact ⟨t,D n [],ht,hh⟩
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table arbitrary m hm
#print axioms never
end BB6Coverage.Agent4LE56
