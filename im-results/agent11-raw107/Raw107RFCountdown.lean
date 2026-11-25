import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw107RFCountdown
open BB6Coverage BB6Coverage.Agent31Pump
inductive V | a | b | c | d | e deriving DecidableEq

def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => match v with
    | .a => some (some ⟨false,true,5⟩)
    | .c => some (some ⟨true,false,4⟩)
    | _ => none
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => match v with
    | .a => some (some ⟨false,true,0⟩)
    | .b => some (some ⟨false,true,1⟩)
    | .c => some (some ⟨true,true,0⟩)
    | _ => none
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => match v with
    | .d => some (some ⟨false,true,2⟩)
    | .e => some (some ⟨false,true,3⟩)
    | _ => none
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,false => some (some ⟨false,true,if v=.d ∨ v=.e then 4 else 2⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none
abbrev Z := [false,false,false]
abbrev O := [true,true,true]
abbrev B := [false,true,true]
abbrev leftTail := [false,false,true,true]
abbrev Dbase (R : List Bool) : Z0 := ⟨3,[true,true],[true,true]++R⟩
abbrev Fcfg (n : Nat) (R : List Bool) : Z0 := ⟨5,R.headD false :: (rep Z n ++ leftTail),R.tail⟩
def family (v : V) (n : Nat) : Z0 := ⟨3,(if v=.d then [false] else [])++rep Z (n+1)++leftTail,[]⟩
def entryCost (v : V) := if v=.d then 11 else 10
def skipCost (v : V) := if v=.c then 5 else 3

theorem entry (v : V) : run0 (table v) (entryCost v) ⟨0,[],[]⟩ = some (family v 0) := by cases v <;> rfl

theorem enter (v : V) (R : List Bool) : run0 (table v) 3 (Dbase R) = some (Fcfg 0 R) := by cases v <;> rfl

theorem skip_one (v : V) (k : Nat) (R : List Bool) :
    run0 (table v) (skipCost v) (Fcfg k (B++R)) = some (Fcfg (k+1) R) := by cases v <;> rfl

theorem skip_all (v : V) (n k : Nat) (R : List Bool) :
    run0 (table v) (skipCost v*n) (Fcfg k (rep B n++R)) = some (Fcfg (k+n) R) := by
  induction n generalizing k with
  | zero => simp [rep,run0]
  | succ n ih =>
    have h := join0 (skip_one v k (rep B n++R)) (ih (k+1))
    simpa only [rep,List.append_assoc,show k+1+n=k+(n+1) by omega,show skipCost v+skipCost v*n=skipCost v*(n+1) by rw [Nat.mul_succ,Nat.add_comm]] using h

theorem triple (v : V) (L R : List Bool) : run0 (table v) 3 ⟨3,Z++L,R⟩ = some ⟨3,L,O++R⟩ := by cases v <;> rfl

theorem restore3 (v : V) (n : Nat) (R : List Bool) :
    run0 (table v) (3*n) ⟨3,rep Z n++leftTail,R⟩ = some ⟨3,leftTail,rep O n++R⟩ := by
  simpa only [List.nil_append] using sweepL (table v) 3 [] [] Z O 3 (triple v) n leftTail R

theorem restore2 (v : V) (R : List Bool) : run0 (table v) 2 ⟨3,leftTail,R⟩ = some (Dbase R) := by cases v <;> rfl

theorem hit (v : V) (n : Nat) (R : List Bool) :
    run0 (table v) 1 (Fcfg n (true::R)) = some ⟨3,rep Z n++leftTail,false::R⟩ := by cases v <;> rfl

def decCost (v : V) (n : Nat) := 3+skipCost v*n+1+3*n+2
theorem decrement (v : V) (n : Nat) (R : List Bool) :
    run0 (table v) (decCost v n) (Dbase (rep B n++true::R)) =
      some (Dbase (rep O n++false::R)) := by
  have h := join0 (enter v (rep B n++true::R)) (skip_all v n 0 (true::R))
  simp only [Nat.zero_add] at h
  exact join0 (join0 (join0 h (hit v n R)) (restore3 v n (false::R))) (restore2 v (rep O n++false::R))

def clearCost (v : V) : Nat → Nat
  | 0 => 0
  | n+1 => clearCost v n + decCost v n + clearCost v n

theorem clear (v : V) (n : Nat) (R : List Bool) :
    run0 (table v) (clearCost v n) (Dbase (rep O n++R)) = some (Dbase (rep B n++R)) := by
  induction n generalizing R with
  | zero => simp [clearCost,rep,run0]
  | succ n ih =>
    have h1 := ih (O++R)
    have h2 := decrement v n (true::true::R)
    have h3 := ih (B++R)
    have h2' : run0 (table v) (decCost v n) (Dbase (rep B n++(O++R))) = some (Dbase (rep O n++(B++R))) := h2
    have h := join0 (join0 h1 h2') h3
    rw [← List.append_assoc,rep_snoc O n,← List.append_assoc,rep_snoc B n] at h
    simpa only [clearCost,rep] using h

theorem overflow (v : V) (hv : v ≠ .d) (n : Nat) : run0 (table v) 2 (Fcfg (n+1) []) = some (family v (n+1)) := by cases v <;> first | contradiction | rfl

def regularCost (v : V) (n : Nat) := 3*(n+1)+2+clearCost v (n+1)+3+skipCost v*(n+1)+2

theorem regularGrowth (v : V) (hv : v ≠ .d) (n : Nat) : run0 (table v) (regularCost v n) (family v n) = some (family v (n+1)) := by
  have h1 := join0 (restore3 v (n+1) []) (restore2 v (rep O (n+1)++[]))
  have h2 := clear v (n+1) []
  have h3 := enter v (rep B (n+1)++[])
  have h4 := skip_all v (n+1) 0 []
  simp only [Nat.zero_add] at h4
  have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) (overflow v hv n)
  simpa only [regularCost,family,if_neg hv,List.nil_append] using h

theorem extraStart (n : Nat) : run0 (table .d) 1 (family .d n) = some ⟨3,rep Z (n+1)++leftTail,[true]⟩ := by rfl

theorem extraOverflow (n : Nat) : run0 (table .d) 3 (Fcfg (n+1) [false]) = some (family .d (n+1)) := by rfl

def extraCost (n : Nat) := 1+3*(n+1)+2+clearCost .d (n+1)+decCost .d (n+1)+clearCost .d (n+1)+3+skipCost .d*(n+1)+3

theorem extraGrowth (n : Nat) : run0 (table .d) (extraCost n) (family .d n) = some (family .d (n+1)) := by
  have h0 := extraStart n
  have h1 := restore3 .d (n+1) [true]
  have h2 := restore2 .d (rep O (n+1)++[true])
  have h3 := clear .d (n+1) [true]
  have h4 := decrement .d (n+1) []
  have h5 := clear .d (n+1) [false]
  have h6 := enter .d (rep B (n+1)++[false])
  have h7 := skip_all .d (n+1) 0 [false]
  simp only [Nat.zero_add] at h7
  exact join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 h0 h1) h2) h3) h4) h5) h6) h7) (extraOverflow n)

def cost (v : V) (n : Nat) := if v=.d then extraCost n else regularCost v n

theorem growth (v : V) (n : Nat) : run0 (table v) (cost v n) (family v n) = some (family v (n+1)) := by
  by_cases h : v=.d
  · subst v; exact extraGrowth n
  · simpa only [cost,if_neg h] using regularGrowth v h n

theorem never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) (family v) (entryCost v) (cost v) (entry v)
    (by intro n; cases v <;> simp [cost,regularCost,extraCost] <;> omega)
    (growth v) m hm

#print axioms entry
#print axioms growth
#print axioms never

namespace M126
abbrev table := _root_.BB6.Agent11Raw107RFCountdown.table .a
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  _root_.BB6.Agent11Raw107RFCountdown.never .a m hm
end M126

namespace M127
abbrev table := _root_.BB6.Agent11Raw107RFCountdown.table .b
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  _root_.BB6.Agent11Raw107RFCountdown.never .b m hm
end M127

namespace M134
abbrev table := _root_.BB6.Agent11Raw107RFCountdown.table .c
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  _root_.BB6.Agent11Raw107RFCountdown.never .c m hm
end M134

namespace M281
abbrev table := _root_.BB6.Agent11Raw107RFCountdown.table .d
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  _root_.BB6.Agent11Raw107RFCountdown.never .d m hm
end M281

namespace M317
abbrev table := _root_.BB6.Agent11Raw107RFCountdown.table .e
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  _root_.BB6.Agent11Raw107RFCountdown.never .e m hm
end M317
end BB6.Agent11Raw107RFCountdown
