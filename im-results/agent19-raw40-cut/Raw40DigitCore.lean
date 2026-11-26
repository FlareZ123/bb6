import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.DigitCore
open BB6Coverage BB6Coverage.Agent31Pump

def z : List Bool := [false,true,true]
def o : List Bool := [true,true,true]
def cfg (r : List Bool) : Z0 := ⟨5,[false],r⟩
def outer (n : Nat) : Z0 := ⟨5,[true,false],rep z (n+2)++[true]⟩

/-- Local macro checks for a three-cell binary digit incrementer.
The arbitrary tails in these equations rule out any reliance on unexamined cells. -/
structure Core (p : PartialMachine) (q : Fin 6) (frame : List Bool) (a t r u v : Nat) : Prop where
  start : ∀ R, run0 p t (cfg (z++R)) = some ⟨q,frame++rep [true] a++[false],R⟩
  one : ∀ L R, run0 p r ⟨q,frame++L,true::R⟩ = some ⟨q,frame++[true]++L,R⟩
  turn : ∀ L R, run0 p u ⟨q,frame++rep [true] a++L,z++R⟩ = some ⟨5,L,z++o++R⟩
  turnEnd : ∀ L, run0 p u ⟨q,frame++rep [true] a++L,[]⟩ = some ⟨5,L,z++[true]⟩
  left : ∀ L R, run0 p 3 ⟨5,o++L,R⟩ = some ⟨5,L,z++R⟩
  prep : ∀ R, run0 p v ⟨5,[true,false],z++z++R⟩ = some (cfg (z++o++o++R))

private theorem repAdd (P : List Bool) (a b : Nat) : rep P (a+b) = rep P a ++ rep P b := by
  induction a with
  | zero => simp [rep]
  | succ a ih =>
    rw [show a+1+b=(a+b)+1 by omega,rep,ih,rep,List.append_assoc]
private theorem rep3 (k : Nat) : rep o k = rep [true] (3*k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [rep,ih,show 3*(k+1)=3+3*k by omega,repAdd]; rfl
private theorem commute (k a : Nat) : rep o k ++ rep [true] a = rep [true] a ++ rep o k := by
  rw [rep3,← repAdd,← repAdd,Nat.add_comm]
private theorem commuteExtra (k a : Nat) :
    [true]++(rep o k++(rep [true] a++[false])) = rep [true] a++(rep o k++[true,false]) := by
  rw [rep3]
  calc
    _ = rep [true] (1+(3*k+a)) ++ [false] := by
      rw [repAdd,repAdd]; simp only [List.append_assoc,show rep [true] 1=[true] by rfl]
    _ = _ := by
      rw [show 1+(3*k+a)=a+(3*k+1) by omega,repAdd,repAdd]
      simp only [List.append_assoc,show rep [true] 1=[true] by rfl,List.cons_append,List.nil_append]

theorem right3 (p : PartialMachine) (q : Fin 6) (frame : List Bool) (a t r u v : Nat)
    (h : Core p q frame a t r u v) (L R : List Bool) :
    run0 p (r+r+r) ⟨q,frame++L,o++R⟩ = some ⟨q,frame++o++L,R⟩ := by
  have h1 := h.one L (true::true::R)
  have h2 := h.one (true::L) (true::R)
  have h3 := h.one (true::true::L) R
  simp only [List.append_assoc,List.cons_append,List.nil_append] at h1 h2 h3
  simpa only [List.append_assoc,o,List.cons_append,List.nil_append] using join0 (join0 h1 h2) h3

def carryCost (t r u k : Nat) := t+(r+r+r)*k+u+3*k

def overflowCost (t r u k : Nat) := t+(r+r+r)*k+r+u+3*k

/-- Increment with k low one-digits followed by a zero, resetting the low digits. -/
theorem carry (p : PartialMachine) (q : Fin 6) (frame : List Bool) (a t r u v : Nat)
    (h : Core p q frame a t r u v) (k : Nat) (R : List Bool) :
    run0 p (carryCost t r u k) (cfg (z++rep o k++z++R)) =
      some (cfg (z++rep z k++o++R)) := by
  have h1 := h.start (rep o k++z++R)
  have h2 := sweepR p q frame [] o o (r+r+r) (right3 p q frame a t r u v h) k (rep [true] a++[false]) (z++R)
  have h3 := h.turn (rep o k++[false]) R
  have h4 := sweepL p 5 [] [] o z 3 h.left k [false] (z++o++R)
  simp only [List.nil_append,List.append_assoc] at h1 h2 h3 h4
  rw [← List.append_assoc (rep o k) (rep [true] a) [false],commute k a,List.append_assoc] at h2
  have H := join0 (join0 (join0 h1 h2) h3) h4
  rw [← List.append_assoc (rep z k) z (o++R),rep_snoc z k] at H
  simpa only [carryCost,cfg,List.append_assoc] using H

/-- Overflow extends the all-zero counter by one digit. -/
theorem overflow (p : PartialMachine) (q : Fin 6) (frame : List Bool) (a t r u v : Nat)
    (h : Core p q frame a t r u v) (k : Nat) :
    run0 p (overflowCost t r u k) (cfg (z++rep o k++[true])) =
      some ⟨5,[true,false],rep z (k+1)++[true]⟩ := by
  have h1 := h.start (rep o k++[true])
  have h2 := sweepR p q frame [] o o (r+r+r) (right3 p q frame a t r u v h) k (rep [true] a++[false]) [true]
  have h3 := h.one (rep o k++rep [true] a++[false]) []
  have h4 := h.turnEnd (rep o k++[true,false])
  have h5 := sweepL p 5 [] [] o z 3 h.left k [true,false] (z++[true])
  simp only [List.nil_append,List.append_assoc] at h1 h2 h3 h4 h5
  rw [commuteExtra k a] at h3
  have H := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  rw [← List.append_assoc (rep z k) z [true],rep_snoc z k] at H
  simpa only [overflowCost,cfg,List.append_assoc,rep] using H

/-- Exact execution cost to fill k zero digits with ones. -/
def fillCost (t r u : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => fillCost t r u k+carryCost t r u k+fillCost t r u k

theorem fill (p : PartialMachine) (q : Fin 6) (frame : List Bool) (m t r u v : Nat) (h : Core p q frame m t r u v) (k : Nat) (R : List Bool) :
    run0 p (fillCost t r u k) (cfg (z++rep z k++R)) = some (cfg (z++rep o k++R)) := by
  induction k generalizing R with
  | zero => simp [fillCost,rep,run0]
  | succ k ih =>
    have h1 := ih (z++R)
    have h2 := carry p q frame m t r u v h k R
    have h3 := ih (o++R)
    simp only [List.append_assoc] at h1 h2 h3
    have H := join0 (join0 h1 h2) h3
    rw [fillCost,show rep z (k+1)=rep z k++z by rw [rep_snoc]; rfl,show rep o (k+1)=rep o k++o by rw [rep_snoc]; rfl]
    simpa only [List.append_assoc] using H

/-- Fill k high zero digits above a already-set low digits. -/
def fillFromCost (t r u a : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => fillFromCost t r u a k+carryCost t r u (a+k)+fillCost t r u (a+k)

theorem fillFrom (p : PartialMachine) (q : Fin 6) (frame : List Bool) (m t r u v : Nat) (h : Core p q frame m t r u v) (a k : Nat) (R : List Bool) :
    run0 p (fillFromCost t r u a k) (cfg (z++rep o a++rep z k++R)) =
      some (cfg (z++rep o (a+k)++R)) := by
  induction k generalizing R with
  | zero => simp [fillFromCost,rep,run0]
  | succ k ih =>
    have h1 := ih (z++R)
    have h2 := carry p q frame m t r u v h (a+k) R
    have h3 := fill p q frame m t r u v h (a+k) (o++R)
    simp only [List.append_assoc] at h1 h2 h3
    have H := join0 (join0 h1 h2) h3
    rw [fillFromCost,show rep z (k+1)=rep z k++z by rw [rep_snoc]; rfl,show a+(k+1)=(a+k)+1 by omega,show rep o ((a+k)+1)=rep o (a+k)++o by rw [rep_snoc]; rfl]
    simpa only [List.append_assoc] using H

def outerCost (t r u v n : Nat) := v+fillFromCost t r u 2 n+overflowCost t r u (2+n)

theorem grow (p : PartialMachine) (q : Fin 6) (frame : List Bool) (m t r u v : Nat) (h : Core p q frame m t r u v) (n : Nat) :
    run0 p (outerCost t r u v n) (outer n) = some (outer (n+1)) := by
  have h1 := h.prep (rep z n++[true])
  have h2 := fillFrom p q frame m t r u v h 2 n [true]
  have h3 := overflow p q frame m t r u v h (2+n)
  have H := join0 (join0 h1 h2) h3
  simpa only [outerCost,outer,show n+2=2+n by omega,repAdd,show rep z 2=z++z by rfl,
    show rep o 2=o++o by rfl,List.append_assoc,show 2+n+1=n+1+2 by omega] using H

theorem never (p : PartialMachine) (q : Fin 6) (frame : List Bool) (m t r u v : Nat) (h : Core p q frame m t r u v) (entry initial : Nat)
    (first : run0 p entry ⟨0,[],[]⟩ = some (outer initial))
    (mach : Machine) (hm : compatible p mach) : NeverHalts mach := by
  apply never_of_growth p (fun n => outer (initial+n)) entry (fun n => outerCost t r u v (initial+n)) _ _ _ mach hm
  · simpa using first
  · intro n; unfold outerCost overflowCost; omega
  · intro n; simpa only [show initial+(n+1)=initial+n+1 by omega] using grow p q frame m t r u v h (initial+n)
#print axioms never
end BB6.Agent19Raw40.DigitCore
