import SweepPumping
import Raw58Live
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent4LF157
open BB6Coverage Agent31Pump
-- 1RB0LF_1RC---_0RD0RF_1LD1RE_0RC0RA_0RE0LD
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨false,true,4⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def D (k : Nat) : Z0 := ⟨3,rep [false,false,false,false] k ++ [false,false,false,false,false,false,false,true,true],[]⟩
def E (k : Nat) (R : List Bool) : Z0 := ⟨4,rep [false,false,false,false] k ++ [false,false,true,true],R⟩

theorem oneComm (k : Nat) (r : List Bool) : true::(rep [true,true,true,true] k ++ r) = rep [true,true,true,true] k ++ true::r := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [rep,List.cons_append,List.nil_append,List.cons.injEq,true_and] using ih

theorem zeroComm (k : Nat) (r : List Bool) : false::(rep [false,false,false,false] k ++ r) = rep [false,false,false,false] k ++ false::r := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [rep,List.cons_append,List.nil_append,List.cons.injEq,true_and] using ih

theorem scan (k : Nat) (R : List Bool) : ∃ t, run0 table t (E 0 (rep [true,true,true,true] k ++ R)) = some (E k R) := by
  induction k generalizing R with
  | zero => exact ⟨0,rfl⟩
  | succ k ih =>
    obtain ⟨a,ha⟩ := ih (true::true::true::true::R)
    have hstart : E 0 (rep [true,true,true,true] (k+1) ++ R) = E 0 (rep [true,true,true,true] k ++ true::true::true::true::R) := by
      apply congrArg (E 0)
      change rep [true,true,true,true] (k+1) ++ R = rep [true,true,true,true] k ++ ([true,true,true,true] ++ R)
      rw [← List.append_assoc,rep_snoc]; rfl
    have h1 : run0 table 3 (E k (true::true::true::true::R)) = some ⟨3,false::(rep [false,false,false,false] k ++ [false,false,true,true]),false::true::true::R⟩ := by
      cases k <;> rfl
    have h2 : run0 table (4*k) ⟨3,false::(rep [false,false,false,false] k ++ [false,false,true,true]),false::true::true::R⟩ =
      some ⟨3,[false,false,false,true,true],rep [true,true,true,true] k ++ false::true::true::R⟩ := by
      rw [zeroComm]
      simpa only [List.nil_append] using sweepL table 3 [] [] [false,false,false,false] [true,true,true,true] 4
        (by intro L R; rfl) k [false,false,false,true,true] (false::true::true::R)
    have h3 : run0 table 7 ⟨3,[false,false,false,true,true],rep [true,true,true,true] k ++ false::true::true::R⟩ = some (E 0 (rep [true,true,true,true] k ++ true::false::true::true::R)) := by
      have H : run0 table 7 ⟨3,[false,false,false,true,true],rep [true,true,true,true] k ++ false::true::true::R⟩ = some (E 0 (true::(rep [true,true,true,true] k ++ false::true::true::R))) := by rfl
      rw [oneComm] at H
      exact H
    obtain ⟨b,hb⟩ := ih (true::false::true::true::R)
    have h4 : run0 table 6 (E k (true::false::true::true::R)) = some (E (k+1) R) := by
      cases k <;> rfl
    rw [hstart]
    exact ⟨_,join0 (join0 (join0 (join0 (join0 ha h1) h2) h3) hb) h4⟩

theorem grow (k : Nat) : ∃ t, 0 < t ∧ run0 table t (D k) = some (D (k+1)) := by
  have h1 : run0 table (4*k) (D k) = some ⟨3,[false,false,false,false,false,false,false,true,true],rep [true,true,true,true] k ++ []⟩ := by
    simpa only [D,List.nil_append] using sweepL table 3 [] [] [false,false,false,false] [true,true,true,true] 4
      (by intro L R; rfl) k [false,false,false,false,false,false,false,true,true] []
  have h2 : run0 table 11 ⟨3,[false,false,false,false,false,false,false,true,true],rep [true,true,true,true] k ++ []⟩ = some (E 0 (true::true::true::true::true::(rep [true,true,true,true] k ++ []))) := by rfl
  have H := join0 h1 h2
  rw [show true::true::true::true::true::(rep [true,true,true,true] k ++ []) = rep [true,true,true,true] (k+1) ++ [true] by
      rw [oneComm k []]; simp only [rep,List.cons_append,List.nil_append]] at H
  obtain ⟨t,h3⟩ := scan (k+1) [true]
  have h4 : run0 table 5 (E (k+1) [true]) = some (D (k+1)) := by
    unfold E D
    simp only [rep,List.cons_append,List.nil_append]
    change run0 table 5 ⟨4,false::false::false::false::(rep [false,false,false,false] k ++ [false,false,true,true]),[true]⟩ = _
    change some (⟨3,false::false::false::false::false::false::false::false::false::(rep [false,false,false,false] k ++ [false,false,true,true]),[]⟩ : Z0) = _
    simp only [zeroComm]
  exact ⟨_,by omega,join0 (join0 H h3) h4⟩

theorem arbitrary (n : Nat) : ∃ t z, n ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some z := by
  have aux : ∀ n : Nat, ∃ t, n ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some (D n) := by
    intro n
    induction n with
    | zero => exact ⟨34,by omega,by rfl⟩
    | succ n ih =>
      obtain ⟨t,ht,hh⟩ := ih
      obtain ⟨u,hu,hr⟩ := grow n
      exact ⟨t+u,by omega,join0 hh hr⟩
  obtain ⟨t,ht,hh⟩ := aux n
  exact ⟨t,D n,ht,hh⟩
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table arbitrary m hm
#print axioms never
end BB6Coverage.Agent4LF157
