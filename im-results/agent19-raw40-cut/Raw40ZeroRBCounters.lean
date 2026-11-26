import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.ZeroRBCounters
open BB6Coverage BB6Coverage.Agent31Pump

/-- Abstract binary counter, least significant digit first. The overflow law
extends the finite tape by a new leading one. -/
structure CounterLaw (p : PartialMachine) (z o : List Bool) (cfg : List Bool → Z0) (cost : Nat → Nat) : Prop where
  carry : ∀ k R, run0 p (cost k) (cfg (rep o k++z++R)) = some (cfg (rep z k++o++R))
  overflow : ∀ k, run0 p (cost k) (cfg (rep o k)) = some (cfg (rep z k++o))

def fillCost (cost : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k+1 => fillCost cost k+cost k+fillCost cost k

theorem fill (p : PartialMachine) (z o : List Bool) (cfg : List Bool → Z0) (cost : Nat → Nat)
    (h : CounterLaw p z o cfg cost) (k : Nat) (R : List Bool) :
    run0 p (fillCost cost k) (cfg (rep z k++R)) = some (cfg (rep o k++R)) := by
  induction k generalizing R with
  | zero => simp [fillCost,rep,run0]
  | succ k ih =>
    have h1 := ih (z++R)
    have h2 := h.carry k R
    have h3 := ih (o++R)
    simp only [List.append_assoc] at h1 h2 h3
    have H := join0 (join0 h1 h2) h3
    rw [fillCost,show rep z (k+1)=rep z k++z by rw [rep_snoc]; rfl,show rep o (k+1)=rep o k++o by rw [rep_snoc]; rfl]
    simpa only [List.append_assoc] using H

def outerCost (cost : Nat → Nat) (k : Nat) := fillCost cost k+cost (k+1)

theorem grow (p : PartialMachine) (z o : List Bool) (cfg : List Bool → Z0) (cost : Nat → Nat)
    (h : CounterLaw p z o cfg cost) (k : Nat) :
    run0 p (outerCost cost k) (cfg (rep z k++o)) = some (cfg (rep z (k+1)++o)) := by
  have H := fill p z o cfg cost h k o
  rw [rep_snoc] at H
  exact join0 H (h.overflow (k+1))

theorem counterNever (p : PartialMachine) (z o : List Bool) (cfg : List Bool → Z0) (cost : Nat → Nat)
    (h : CounterLaw p z o cfg cost) (pos : ∀ k, 0<cost k) (entry : Nat)
    (first : run0 p entry ⟨0,[],[]⟩ = some (cfg o)) (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_growth p (fun k => cfg (rep z k++o)) entry (outerCost cost) _ _ _ m hm
  · simpa only [rep,List.nil_append] using first
  · intro k; unfold outerCost; have := pos (k+1); omega
  · exact grow p z o cfg cost h

def U : List Bool := [true,true,true]
def Z : List Bool := [false,false,false]

namespace Leaf382
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,true,5⟩)
  | _,_ => none
def cfg (R : List Bool) : Z0 := ⟨0,[false],Z++R⟩
def scan (k : Nat) (R : List Bool) : Z0 := ⟨5,U++rep U k++[false],R⟩
def erase (k : Nat) (R : List Bool) : Z0 := ⟨4,U++rep U k++[false],R⟩
theorem prep (R : List Bool) : run0 table 11 (cfg R) = some (scan 0 R) := by rfl
theorem scanBlock (L R : List Bool) : run0 table 3 ⟨5,U++L,U++R⟩ = some ⟨5,U++U++L,R⟩ := by rfl
theorem turn (L R : List Bool) : run0 table 10 ⟨5,U++L,Z++R⟩ = some ⟨4,U++L,U++R⟩ := by rfl
theorem turnBlank (L : List Bool) : run0 table 10 ⟨5,U++L,[]⟩ = some ⟨4,U++L,U⟩ := by rfl
theorem eraseBlock (L R : List Bool) : run0 table 3 ⟨4,U++L,R⟩ = some ⟨4,L,Z++R⟩ := by rfl
theorem reset (R : List Bool) : run0 table 2 ⟨4,[false],Z++R⟩ = some (cfg R) := by rfl

theorem scanAll (k : Nat) (R : List Bool) : run0 table (11+3*k) (cfg (rep U k++R)) = some (scan k R) := by
  have h := sweepR table 5 U [] U U 3 scanBlock k [false] R
  simp only [List.nil_append,List.append_assoc] at h
  exact join0 (prep (rep U k++R)) h

theorem eraseAll (k : Nat) (R : List Bool) : run0 table (3*(k+1)+2) (erase k R) = some (cfg (rep Z k++R)) := by
  have h := sweepL table 4 [] [] U Z 3 eraseBlock (k+1) [false] R
  simp only [List.nil_append,rep,List.append_assoc] at h
  exact join0 h (reset (rep Z k++R))

def cost (k : Nat) := 6*k+26

theorem law : CounterLaw table Z U cfg cost := by
  constructor
  · intro k R
    have h1 := scanAll k (Z++R)
    have h2 := turn (rep U k++[false]) R
    have h3 := eraseAll k (U++R)
    simp only [scan,erase,List.append_assoc] at h1 h2 h3
    have H := join0 (join0 h1 h2) h3
    rw [show 11+3*k+10+(3*(k+1)+2)=cost k by unfold cost; omega] at H
    simpa only [List.append_assoc] using H
  · intro k
    have h1 := scanAll k []
    have h2 := turnBlank (rep U k++[false])
    have h3 := eraseAll k U
    simp only [scan,erase,List.append_assoc,List.append_nil] at h1 h2 h3
    have H := join0 (join0 h1 h2) h3
    rw [show 11+3*k+10+(3*(k+1)+2)=cost k by unfold cost; omega] at H
    exact H

theorem entry : run0 table 26 ⟨0,[],[]⟩ = some (cfg U) := by rfl
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  counterNever table Z U cfg cost law (by intro k; unfold cost; omega) 26 entry m hm
#print axioms never
end Leaf382

namespace Leaf878
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
def cfg (R : List Bool) : Z0 := ⟨0,[false,false],Z++R⟩
def frame : List Bool := [true,false,true,true]
def scan (k : Nat) (R : List Bool) : Z0 := ⟨1,frame++rep U k++[false],R⟩
def erase (k : Nat) (R : List Bool) : Z0 := ⟨5,U++rep U k++[false],false::R⟩
theorem prep (R : List Bool) : run0 table 13 (cfg R) = some (scan 0 R) := by rfl
theorem scanBlock (L R : List Bool) : run0 table 9 ⟨1,frame++L,U++R⟩ = some ⟨1,frame++U++L,R⟩ := by rfl
theorem turn (L R : List Bool) : run0 table 11 ⟨1,frame++L,Z++R⟩ = some ⟨5,U++L,false::(U++R)⟩ := by rfl
theorem turnBlank (L : List Bool) : run0 table 11 ⟨1,frame++L,[]⟩ = some ⟨5,U++L,false::U⟩ := by rfl
theorem eraseBlock (L R : List Bool) : run0 table 3 ⟨5,U++L,R⟩ = some ⟨5,L,Z++R⟩ := by rfl
theorem reset (R : List Bool) : run0 table 1 ⟨5,[false],false::(Z++R)⟩ = some (cfg R) := by rfl

theorem scanAll (k : Nat) (R : List Bool) : run0 table (13+9*k) (cfg (rep U k++R)) = some (scan k R) := by
  have h := sweepR table 1 frame [] U U 9 scanBlock k [false] R
  simp only [List.nil_append,List.append_assoc] at h
  exact join0 (prep (rep U k++R)) h

theorem eraseAll (k : Nat) (R : List Bool) : run0 table (3*(k+1)+1) (erase k R) = some (cfg (rep Z k++R)) := by
  have h := sweepL table 5 [] [] U Z 3 eraseBlock (k+1) [false] (false::R)
  simp only [List.nil_append] at h
  have eq : rep Z (k+1)++false::R = false::(rep Z (k+1)++R) := by
    change rep Z (k+1)++([false]++R) = [false]++(rep Z (k+1)++R)
    rw [← List.append_assoc,← show [false]++rep Z (k+1)=rep Z (k+1)++[false] from rotate false [false,false] (k+1),List.append_assoc]
  rw [eq] at h
  simp only [rep,List.append_assoc] at h
  exact join0 h (reset (rep Z k++R))

def cost (k : Nat) := 12*k+28

theorem law : CounterLaw table Z U cfg cost := by
  constructor
  · intro k R
    have h1 := scanAll k (Z++R)
    have h2 := turn (rep U k++[false]) R
    have h3 := eraseAll k (U++R)
    simp only [scan,erase,List.append_assoc] at h1 h2 h3
    have H := join0 (join0 h1 h2) h3
    rw [show 13+9*k+11+(3*(k+1)+1)=cost k by unfold cost; omega] at H
    simpa only [List.append_assoc] using H
  · intro k
    have h1 := scanAll k []
    have h2 := turnBlank (rep U k++[false])
    have h3 := eraseAll k U
    simp only [scan,erase,List.append_assoc,List.append_nil] at h1 h2 h3
    have H := join0 (join0 h1 h2) h3
    rw [show 13+9*k+11+(3*(k+1)+1)=cost k by unfold cost; omega] at H
    exact H

theorem entry : run0 table 28 ⟨0,[],[]⟩ = some (cfg U) := by rfl
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  counterNever table Z U cfg cost law (by intro k; unfold cost; omega) 28 entry m hm
#print axioms never
end Leaf878

namespace Leaf110
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,false,0⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | _,_ => none
def U : List Bool := [true,true]
def Z : List Bool := [false,false]
def cfg (R : List Bool) : Z0 := ⟨0,[false,false],false::R⟩
def scan (k : Nat) (R : List Bool) : Z0 := ⟨1,[false]++rep Z k++[true,false],R⟩

theorem prep (R : List Bool) : run0 table 1 (cfg R) = some (scan 0 R) := by rfl
theorem scanBlock (L R : List Bool) : run0 table 6 ⟨1,[false]++L,U++R⟩ = some ⟨1,[false]++Z++L,R⟩ := by rfl
theorem scanAll (k : Nat) (R : List Bool) : run0 table (1+6*k) (cfg (rep U k++R)) = some (scan k R) := by
  have h := sweepR table 1 [false] [] U Z 6 scanBlock k [true,false] R
  simp only [List.nil_append,List.append_assoc] at h
  exact join0 (prep (rep U k++R)) h

theorem turn0 (R : List Bool) : run0 table 9 (scan 0 (Z++R)) = some (cfg (U++R)) := by rfl
theorem turn0Blank : run0 table 9 (scan 0 []) = some (cfg U) := by rfl

theorem turn (L R : List Bool) : run0 table 6 ⟨1,[false,false,false]++L,Z++R⟩ = some ⟨1,[true,true,false]++L,U++R⟩ := by rfl
theorem turnBlank (L : List Bool) : run0 table 6 ⟨1,[false,false,false]++L,[]⟩ = some ⟨1,[true,true,false]++L,U⟩ := by rfl

theorem eraseBlock (L R : List Bool) : run0 table 6 ⟨1,[true,true]++Z++L,R⟩ = some ⟨1,[true,true]++L,Z++R⟩ := by rfl

theorem reset (R : List Bool) : run0 table 9 ⟨1,[true,true,false,true,false],R⟩ = some ⟨0,[false,false],[false,false,false]++R⟩ := by rfl

theorem eraseAll (k : Nat) (R : List Bool) : run0 table (6*k+9) ⟨1,[true,true,false]++rep Z k++[true,false],R⟩ = some (cfg (rep Z (k+1)++R)) := by
  have h := sweepL table 1 [true,true] [] Z Z 6 eraseBlock k [false,true,false] R
  simp only [List.nil_append,List.append_assoc] at h
  have eq : [true,true,false]++(rep Z k++[true,false]) = [true,true]++(rep Z k++[false,true,false]) := by
    have hr := rotate false [false] k
    change [false]++rep Z k = rep Z k++[false] at hr
    change [true,true]++([false]++(rep Z k++[true,false])) = _
    rw [← List.append_assoc [false],hr,List.append_assoc]
    rfl
  have h' : run0 table (6*k) ⟨1,[true,true,false]++rep Z k++[true,false],R⟩ = some ⟨1,[true,true,false,true,false],rep Z k++R⟩ := by
    change run0 table (6*k) ⟨1,[true,true,false]++rep Z k++[true,false],R⟩ = some ⟨1,[true,true]++[false,true,false],rep Z k++R⟩
    simpa only [List.append_assoc,eq] using h
  have H := join0 h' (reset (rep Z k++R))
  change run0 table (6*k+9) ⟨1,[true,true,false]++rep Z k++[true,false],R⟩ = some ⟨0,[false,false],[false,false,false]++(rep Z k++R)⟩
  exact H

def cost (k : Nat) := 12*k+10

theorem law : CounterLaw table Z U cfg cost := by
  constructor
  · intro k R
    cases k with
    | zero =>
      have H := join0 (prep (Z++R)) (turn0 R)
      exact H
    | succ k =>
      have h1 := scanAll (k+1) (Z++R)
      have h2 := turn (rep Z k++[true,false]) R
      have h3 := eraseAll k (U++R)
      simp only [scan,rep,List.append_assoc] at h1
      simp only [List.append_assoc] at h2 h3
      have H := join0 (join0 h1 h2) h3
      rw [show 1+6*(k+1)+6+(6*k+9)=cost (k+1) by unfold cost; omega] at H
      simpa only [rep,List.append_assoc] using H
  · intro k
    cases k with
    | zero =>
      have H := join0 (prep []) turn0Blank
      exact H
    | succ k =>
      have h1 := scanAll (k+1) []
      have h2 := turnBlank (rep Z k++[true,false])
      have h3 := eraseAll k U
      simp only [scan,rep,List.append_assoc,List.append_nil] at h1
      simp only [List.append_assoc] at h2 h3
      have H := join0 (join0 h1 h2) h3
      rw [show 1+6*(k+1)+6+(6*k+9)=cost (k+1) by unfold cost; omega] at H
      exact H

theorem entry : run0 table 10 ⟨0,[],[]⟩ = some (cfg U) := by rfl
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  counterNever table Z U cfg cost law (by intro k; unfold cost; omega) 10 entry m hm
#print axioms never
end Leaf110
end BB6.Agent19Raw40.ZeroRBCounters
