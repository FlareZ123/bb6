import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent40Raw57Alternating
open BB6Coverage BB6Coverage.Agent31Pump

/-- v=false is Raw57/1LA row 748, v=true is row 944. F0 is the only hole. -/
def table (v : Bool) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false, v, if v then 3 else 5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,true,2⟩)
  | _,_ => none
abbrev z : Bool := false
abbrev o : Bool := true
abbrev P : List Bool := [z,o]
abbrev Q : List Bool := [z,o,z,o]
abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev F (L R : List Bool) : Z0 := ⟨5,L,R⟩
def startCost (v : Bool) : Nat := if v then 4 else 6
def backCost (v : Bool) : Nat := if v then 14 else 18
def finishCost (v : Bool) : Nat := if v then 13 else 17
def emptyCost (v : Bool) : Nat := if v then 15 else 17
def carryCost (v : Bool) : Nat := if v then 17 else 19
def carryCost2 (v : Bool) : Nat := if v then 15 else 19

theorem startMacro (v : Bool) (R : List Bool) :
    run0 (table v) (startCost v) (A [] ([o,o,z,o]++R)) = some (F [o,z,o,z,o] R) := by cases v <;> rfl

theorem scanMacro (v : Bool) (L R : List Bool) :
    run0 (table v) 4 (F (o::L) (Q++R)) = some (F (o::(Q++L)) R) := by cases v <;> rfl

theorem turnMacro (v : Bool) (L R : List Bool) :
    run0 (table v) 13 (F ([o,z,o]++L) ([o,z]++R)) = some (A L ([o,o,o,z,o]++R)) := by cases v <;> rfl

theorem turnLast (v : Bool) (L : List Bool) :
    run0 (table v) 13 (F ([o,z,o]++L) [o]) = some (A L [o,o,o,z,o]) := by cases v <;> rfl

theorem turnEmpty (v : Bool) (L : List Bool) :
    run0 (table v) (emptyCost v) (F ([o,z,o]++L) []) = some (A L [o,o,z,o,o]) := by cases v <;> rfl

theorem carry1 (v : Bool) (L : List Bool) :
    run0 (table v) (carryCost v) (A (P++L) [o,o,z,o,o]) = some (A ([z,o,o]++L) [o,o,o,z,o]) := by cases v <;> rfl

theorem carry2 (v : Bool) (L : List Bool) :
    run0 (table v) (carryCost2 v) (A ([z,o,o]++L) [o,o,o,z,o]) = some (A L [o,o,o,o,z,o,z,o]) := by cases v <;> rfl

theorem backMacro (v : Bool) (L R : List Bool) :
    run0 (table v) (backCost v) (A (P++L) ([o,o,o]++R)) = some (A L ([o,o,o]++P++R)) := by cases v <;> rfl

theorem finishMacro (v : Bool) (R : List Bool) :
    run0 (table v) (finishCost v) (A [] ([o,o,o]++R)) = some (A [] ([o,o]++P++R)) := by cases v <;> rfl

theorem pair_double (n : Nat) : rep P (2*n) = rep Q n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega]
    simp only [rep,ih]
    rfl

theorem pair_odd (n : Nat) : rep P (2*n+1) = P++rep Q n := by
  rw [rep,pair_double]

def sect (n : Nat) (R : List Bool) : Z0 := A [] ([o,o]++rep P (2*n+1)++R)

theorem scan (v : Bool) (n : Nat) (R : List Bool) :
    run0 (table v) (startCost v+4*n) (sect n R) = some (F ([o,z,o]++rep P (2*n+1)) R) := by
  have h1 := startMacro v (rep Q n++R)
  have h2 := sweepR (table v) 5 [o] [] Q Q 4
    (fun L R => by simpa only [List.nil_append,List.cons_append] using scanMacro v L R) n Q R
  have h := join0 h1 h2
  simp only [List.append_assoc,List.nil_append] at h
  rw [rep_snoc Q n] at h
  rw [sect,pair_odd]
  simpa only [List.nil_append,List.append_assoc,List.cons_append] using h

theorem drain (v : Bool) (k : Nat) (R : List Bool) :
    run0 (table v) (backCost v*k) (A (rep P k) ([o,o,o]++R)) = some (A [] ([o,o,o]++rep P k++R)) := by
  have h := sweepL (table v) 0 [] [o,o,o] P P (backCost v)
    (fun L R => by simpa only [List.nil_append,List.append_assoc] using backMacro v L R) k [] R
  simpa only [List.nil_append,List.append_nil] using h

def incCost (v : Bool) (n : Nat) : Nat := startCost v+4*n+13+backCost v*(2*n+1)+finishCost v

theorem advance (v : Bool) (n : Nat) (R : List Bool) :
    run0 (table v) (incCost v n) (sect n ([o,z]++R)) = some (sect (n+1) R) := by
  have h1 := scan v n ([o,z]++R)
  have h2 := turnMacro v (rep P (2*n+1)) R
  have h3 := drain v (2*n+1) (P++R)
  have h4 := finishMacro v (rep P (2*n+1)++(P++R))
  have h := join0 (join0 (join0 h1 h2) h3) h4
  have e : 2*(n+1)+1=2*n+1+1+1 := by omega
  unfold sect
  rw [e]
  have he : rep P (2*n+1)++(P++R) = P++(rep P (2*n+1)++R) := by rw [← List.append_assoc,rep_snoc,List.append_assoc]
  rw [he] at h
  simpa only [incCost,sect,rep,List.append_assoc,List.cons_append] using h

theorem advanceLast (v : Bool) (n : Nat) :
    run0 (table v) (incCost v n) (sect n [o]) = some (sect (n+1) []) := by
  have h1 := scan v n [o]
  have h2 := turnLast v (rep P (2*n+1))
  have h3 := drain v (2*n+1) P
  have h4 := finishMacro v (rep P (2*n+1)++P)
  have h := join0 (join0 (join0 h1 h2) h3) h4
  have e : 2*(n+1)+1=2*n+1+1+1 := by omega
  unfold sect
  rw [e]
  rw [rep_snoc P (2*n+1)] at h
  simpa only [incCost,sect,rep,List.append_assoc,List.cons_append,List.append_nil] using h

def resetCost (v : Bool) (n : Nat) : Nat := startCost v+4*n+emptyCost v+carryCost v+carryCost2 v+backCost v*(2*n)+finishCost v

theorem reset (v : Bool) (n : Nat) :
    run0 (table v) (resetCost v n) (sect n []) = some (sect n [o,z,o,z,o]) := by
  have h1 := scan v n []
  have h2 := turnEmpty v (rep P (2*n+1))
  have h12 := join0 h1 h2
  rw [rep] at h12
  have h3 := carry1 v (rep P (2*n))
  have h4 := carry2 v (rep P (2*n))
  have h5 := drain v (2*n) [o,z,o,z,o]
  have h6 := finishMacro v (rep P (2*n)++[o,z,o,z,o])
  have h := join0 (join0 (join0 (join0 h12 h3) h4) h5) h6
  simpa only [resetCost,sect,rep,List.append_assoc,List.cons_append] using h

def epochCost (v : Bool) (n : Nat) : Nat := resetCost v n + incCost v n + incCost v (n+1) + incCost v (n+2)

theorem epoch (v : Bool) (n : Nat) :
    run0 (table v) (epochCost v n) (sect n []) = some (sect (n+3) []) := by
  exact join0 (join0 (join0 (reset v n) (advance v n [o,z,o])) (advance v (n+1) [o])) (advanceLast v (n+2))

theorem entry (v : Bool) : run0 (table v) 9 ⟨0,[],[]⟩ = some (sect 0 []) := by cases v <;> rfl

theorem epochCost_formula (v : Bool) (n : Nat) :
    epochCost v n = if v then 292+128*n else 360+160*n := by
  cases v <;> simp [epochCost,resetCost,incCost,startCost,emptyCost,carryCost,carryCost2,backCost,finishCost] <;> omega

theorem growth (v : Bool) (k : Nat) :
    run0 (table v) (epochCost v (3*k)) (sect (3*k) []) = some (sect (3*(k+1)) []) := by
  simpa only [show 3*(k+1)=3*k+3 by omega] using epoch v (3*k)

theorem live_prefix (v : Bool) (k : Nat) :
    ∃ t, k ≤ t ∧ run0 (table v) t ⟨0,[],[]⟩ = some (sect (3*k) []) := by
  induction k with
  | zero => exact ⟨9,by omega,entry v⟩
  | succ k ih =>
    obtain ⟨t,ht,hr⟩ := ih
    have hp : 0 < epochCost v (3*k) := by rw [epochCost_formula]; cases v <;> simp <;> omega
    exact ⟨t+epochCost v (3*k),by omega,join0 hr (growth v k)⟩

theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) (fun k => sect (3*k) []) 9 (fun k => epochCost v (3*k))
    (entry v) (by intro k; rw [epochCost_formula]; cases v <;> simp <;> omega)
    (growth v) m hm

#print axioms never
#print axioms growth
#print axioms live_prefix
#print axioms epochCost_formula
#print axioms epoch
#print axioms entry
end BB6Coverage.Agent40Raw57Alternating

namespace BB6Coverage.Agent40Raw57Alternating.M748
open BB6Coverage
abbrev table := Agent40Raw57Alternating.table false
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent40Raw57Alternating.never false m hm
#print axioms never
end BB6Coverage.Agent40Raw57Alternating.M748

namespace BB6Coverage.Agent40Raw57Alternating.M944
open BB6Coverage
abbrev table := Agent40Raw57Alternating.table true
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent40Raw57Alternating.never true m hm
#print axioms never
end BB6Coverage.Agent40Raw57Alternating.M944
