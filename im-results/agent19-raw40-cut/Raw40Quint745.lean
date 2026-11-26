import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.Quint745
open BB6Coverage BB6Coverage.Agent31Pump
-- 1RB1RC_1RC0LF_0RD1RE_1LD1LA_---0RF_0RC0LD
-- E0 remains free.
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def digit : Nat → List Bool
  | 0 => [false,false,true]
  | 1 => [true,false,false]
  | 2 => [false,false,false]
  | 3 => [true,true,true]
  | _ => [false,true,true]
def cfg (R : List Bool) : Z0 := ⟨3,[true,true],true::R⟩
def turnCost : Nat → Nat
  | 0 => 9
  | 1 => 3
  | 2 => 7
  | _ => 3

theorem start (R : List Bool) : run0 table 3 (cfg R) = some ⟨4,[true,true,true],R⟩ := by rfl
theorem scan (L R : List Bool) : run0 table 3 ⟨4,[true,true]++L,digit 4++R⟩ = some ⟨4,[true,true]++digit 0++L,R⟩ := by rfl
theorem restore (L R : List Bool) : run0 table 5 ⟨3,[true]++digit 0++L,[true]++R⟩ = some ⟨3,[true]++L,[true]++digit 0++R⟩ := by rfl
theorem turn (d : Nat) (hd : d < 4) (L R : List Bool) :
    run0 table (turnCost d) ⟨4,[true,true]++L,digit d++R⟩ = some ⟨3,[true]++L,[true]++digit (d+1)++R⟩ := by
  have h : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;> rfl
theorem turnEnd (L : List Bool) : run0 table 7 ⟨4,[true,true]++L,[]⟩ = some ⟨3,[true]++L,[true]++digit 3⟩ := by rfl

def carryCost (d k : Nat) := 3+3*k+turnCost d+5*k
theorem carry (d : Nat) (hd : d < 4) (k : Nat) (R : List Bool) :
    run0 table (carryCost d k) (cfg (rep (digit 4) k++digit d++R)) = some (cfg (rep (digit 0) k++digit (d+1)++R)) := by
  have h1 := start (rep (digit 4) k++digit d++R)
  have h2 := sweepR table 4 [true,true] [] (digit 4) (digit 0) 3 (by simpa using scan) k [true] (digit d++R)
  have h3 := turn d hd (rep (digit 0) k++[true]) R
  have h4 := sweepL table 3 [true] [true] (digit 0) (digit 0) 5 restore k [true] (digit (d+1)++R)
  simp only [List.nil_append,List.append_assoc,List.singleton_append] at h1 h2 h3 h4
  have H := join0 (join0 (join0 h1 h2) h3) h4
  simpa only [carryCost,cfg,List.append_assoc,List.singleton_append,List.cons_append] using H

def overflowCost (k : Nat) := 3+3*k+7+5*k
theorem overflow (k : Nat) :
    run0 table (overflowCost k) (cfg (rep (digit 4) k)) = some (cfg (rep (digit 0) k++digit 3)) := by
  have h1 := start (rep (digit 4) k)
  have h2 := sweepR table 4 [true,true] [] (digit 4) (digit 0) 3 (by simpa using scan) k [true] []
  have h3 := turnEnd (rep (digit 0) k++[true])
  have h4 := sweepL table 3 [true] [true] (digit 0) (digit 0) 5 restore k [true] (digit 3)
  simp only [List.nil_append,List.append_nil,List.append_assoc,List.singleton_append] at h1 h2 h3 h4
  have H := join0 (join0 (join0 h1 h2) h3) h4
  exact H

private theorem repLast (P : List Bool) (k : Nat) : rep P (k+1)=rep P k++P := by rw [rep_snoc]; rfl

def fillCost : Nat → Nat
  | 0 => 0
  | k+1 => fillCost k+carryCost 0 k+fillCost k+carryCost 1 k+fillCost k+carryCost 2 k+fillCost k+carryCost 3 k+fillCost k

theorem fill (k : Nat) (R : List Bool) : run0 table (fillCost k) (cfg (rep (digit 0) k++R)) = some (cfg (rep (digit 4) k++R)) := by
  induction k generalizing R with
  | zero => simp [fillCost,rep,run0]
  | succ k ih =>
    have h0 := ih (digit 0++R)
    have h1 := carry 0 (by decide) k R
    have h2 := ih (digit 1++R)
    have h3 := carry 1 (by decide) k R
    have h4 := ih (digit 2++R)
    have h5 := carry 2 (by decide) k R
    have h6 := ih (digit 3++R)
    have h7 := carry 3 (by decide) k R
    have h8 := ih (digit 4++R)
    simp only [List.append_assoc] at h0 h1 h2 h3 h4 h5 h6 h7 h8
    have H := join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 h0 h1) h2) h3) h4) h5) h6) h7) h8
    simpa only [fillCost,repLast,List.append_assoc] using H

def family (n : Nat) := cfg (rep (digit 0) n++digit 3)
def outerCost (n : Nat) := fillCost n+carryCost 3 n+fillCost n+overflowCost (n+1)
theorem grow (n : Nat) : run0 table (outerCost n) (family n) = some (family (n+1)) := by
  have h1 := fill n (digit 3)
  have h2 := carry 3 (by decide) n []
  have h3 := fill n (digit 4)
  have h4 := overflow (n+1)
  simp only [List.append_nil] at h2
  rw [← repLast] at h3
  exact join0 (join0 (join0 h1 h2) h3) h4

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply never_of_growth table family 21 outerCost (by rfl) _ grow m hm
  intro n; unfold outerCost overflowCost; omega
#print axioms never
end BB6.Agent19Raw40.Quint745
