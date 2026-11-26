import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw391LEBinarySix
open BB6Coverage BB6Coverage.Agent31Pump

inductive V where
  | a | b | c | d | e | f
  deriving DecidableEq
-- 1897, 2372, 2529, 2534, 2535, 2550 respectively.
def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some (match v with | .b => ⟨true,true,5⟩ | .d => ⟨false,true,4⟩ | _ => ⟨true,false,1⟩))
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some (match v with | .a => ⟨false,false,5⟩ | .b => ⟨true,false,1⟩ | _ => ⟨true,false,5⟩))
  | 5,false => match v with
      | .a => some (some ⟨true,true,0⟩) | .b => none | .c => some (some ⟨true,false,0⟩)
      | .d | .e => some (some ⟨true,false,1⟩) | .f => some (some ⟨true,true,1⟩)
  | 5,true => match v with | .b => some (some ⟨true,false,4⟩) | _ => none
  | _,_ => none

abbrev O := rep [true]
abbrev Z := rep [false]
def R (n : Nat) := true::true::O n

def extra : V → List Bool | .b => [] | .c => [false,false] | _ => [false]
def Apre (v : V) := [true,false,false,false]++extra v
def Bpre (v : V) := [true,true,false,false]++extra v
def Cpre (v : V) := [true,true,false,true,true]++extra v

def A (v : V) (P : List Bool) (n : Nat) : Z0 := ⟨3,Apre v++P,R n⟩
def B (v : V) (P : List Bool) (n : Nat) : Z0 := ⟨3,Bpre v++P,R n⟩
def C (v : V) (P : List Bool) (n : Nat) : Z0 := ⟨3,Cpre v++P,R n⟩

def suffix : V → List Bool
  | .b => [true,false,true,false]
  | .c => [true,true,true,false,true,false]
  | _ => [true,true,false,true,false]
def beginCost : V → Nat | .a => 12 | .b => 7 | .c => 11 | .d | .e => 8 | .f => 10
def shiftCost : V → Nat | .b | .d => 3 | _ => 1
def finishCost : V → Nat | .b => 12 | .c => 10 | .d => 13 | _ => 9

def scan (v : V) (P : List Bool) (k n : Nat) : Z0 := ⟨1,P,true::(O k++suffix v++R n)⟩

private theorem cOne (v : V) (L T : List Bool) :
    run0 (table v) 1 ⟨2,true::L,true::T⟩ = some ⟨2,true::false::L,T⟩ := by
  cases v <;> rfl
private theorem dOne (v : V) (L T : List Bool) :
    run0 (table v) 1 ⟨3,false::L,T⟩ = some ⟨3,L,true::T⟩ := by
  cases v <;> rfl
private theorem cSweep (v : V) (n : Nat) (L T : List Bool) :
    run0 (table v) n ⟨2,true::L,O n++T⟩ = some ⟨2,true::(Z n++L),T⟩ := by
  simpa only [List.singleton_append,List.nil_append,List.cons_append,Nat.one_mul] using
    sweepR (table v) 2 [true] [] [true] [false] 1 (by intro L T; exact cOne v L T) n L T
private theorem dSweep (v : V) (n : Nat) (L T : List Bool) :
    run0 (table v) n ⟨3,Z n++L,T⟩ = some ⟨3,L,O n++T⟩ := by
  simpa only [List.nil_append,Nat.one_mul] using
    sweepL (table v) 3 [] [] [false] [true] 1 (by simpa only [List.singleton_append,List.nil_append] using dOne v) n L T
private theorem turn (v : V) (L : List Bool) :
    run0 (table v) 3 ⟨2,true::L,[]⟩ = some ⟨3,false::false::L,[true]⟩ := by
  cases v <;> rfl
private theorem back (v : V) (n : Nat) (L : List Bool) :
    run0 (table v) (n+3+(n+2)) ⟨2,true::L,O n⟩ = some ⟨3,L,O (n+3)⟩ := by
  have h1 := cSweep v n L []
  rw [List.append_nil] at h1
  have h2 := turn v (Z n++L)
  have h3 := dSweep v (n+2) L [true]
  have h4 : O (n+2)++[true] = O (n+3) := by
    rw [rep_snoc]; rfl
  rw [h4] at h3
  exact join0 (join0 h1 h2) h3

private theorem stageA (v : V) (P : List Bool) (n : Nat) :
    run0 (table v) 5 (A v P n) = some ⟨2,true::(Bpre v++P),O (n+1)⟩ := by
  cases v <;> rfl
private theorem stageB (v : V) (P : List Bool) (n : Nat) :
    run0 (table v) 14 (B v P n) = some ⟨2,true::(Cpre v++P),O n⟩ := by
  cases v <;> rfl
private theorem stageC (v : V) (P : List Bool) (n : Nat) :
    run0 (table v) (beginCost v) (C v P n) = some (scan v P 0 n) := by
  cases v <;> rfl
private theorem scanOne (v : V) (P : List Bool) (k n : Nat) :
    run0 (table v) (shiftCost v) (scan v (true::P) k n) = some (scan v P (k+1) n) := by
  cases v <;> rfl
private theorem scanZero (v : V) (P : List Bool) (k n : Nat) :
    run0 (table v) 1 (scan v (false::P) k n) = some ⟨2,[true,true]++P,O k++suffix v++R n⟩ := by
  cases v <;> rfl
private theorem scanNil (v : V) (k n : Nat) :
    run0 (table v) 1 (scan v [] k n) = some ⟨2,[true,true],O k++suffix v++R n⟩ := by
  cases v <;> rfl
private theorem finish (v : V) (L : List Bool) (n : Nat) :
    run0 (table v) (finishCost v) ⟨2,true::L,suffix v++R n⟩ = some ⟨2,true::(Apre v++L),R n⟩ := by
  cases v <;> rfl
private theorem reset (v : V) (P : List Bool) (k n : Nat) :
    ∃ t, 0 < t ∧ run0 (table v) t ⟨2,[true,true]++P,O k++suffix v++R n⟩ =
      some (A v (Z k++true::P) (n+3)) := by
  have h1 := cSweep v k (true::P) (suffix v++R n)
  have h2 := finish v (Z k++true::P) n
  have h3 := back v (n+2) (Apre v++(Z k++true::P))
  refine ⟨k+finishCost v+(n+2+3+(n+2+2)),by omega,?_⟩
  rw [List.append_assoc]
  exact join0 (join0 h1 h2) h3

/-- Arbitrary binary tail, rather than a bounded counter. -/
private theorem carry (v : V) (P : List Bool) (k n : Nat) :
    ∃ t T, 0 < t ∧ run0 (table v) t (scan v P k n) = some (A v T (n+3)) := by
  induction P generalizing k with
  | nil =>
    obtain ⟨t,ht,hr⟩ := reset v [] k n
    exact ⟨1+t,_,by omega,join0 (scanNil v k n) hr⟩
  | cons b P ih =>
    cases b with
    | false =>
      obtain ⟨t,ht,hr⟩ := reset v P k n
      exact ⟨1+t,_,by omega,join0 (scanZero v P k n) hr⟩
    | true =>
      obtain ⟨t,T,ht,hr⟩ := ih (k+1)
      exact ⟨shiftCost v+t,T,by omega,join0 (scanOne v P k n) hr⟩

inductive Good (v : V) : Z0 → Prop
  | a (P : List Bool) (n : Nat) : Good v (A v P n)
  | b (P : List Bool) (n : Nat) : Good v (B v P n)
  | c (P : List Bool) (n : Nat) : Good v (C v P n)

theorem next (v : V) {z : Z0} (h : Good v z) :
    ∃ t z', 0 < t ∧ Good v z' ∧ run0 (table v) t z = some z' := by
  cases h with
  | a P n =>
    exact ⟨_,_,by omega,Good.b P (n+2),join0 (stageA v P n) (back v (n+1) (Bpre v++P))⟩
  | b P n =>
    exact ⟨_,_,by omega,Good.c P (n+1),join0 (stageB v P n) (back v n (Cpre v++P))⟩
  | c P n =>
    obtain ⟨t,T,ht,hr⟩ := carry v P 0 n
    exact ⟨beginCost v+t,_,by omega,Good.a T (n+3),join0 (stageC v P n) hr⟩

def entryCost : V → Nat | .a => 57 | .b => 55 | .c => 57 | .d => 57 | .e => 53 | .f => 55
private theorem entry (v : V) : run0 (table v) (entryCost v) ⟨0,[],[]⟩ = some (A v [true] 4) := by
  cases v <;> rfl

theorem live (v : V) (n : Nat) : ∃ k z, n ≤ k ∧ Good v z ∧ run0 (table v) k ⟨0,[],[]⟩ = some z := by
  induction n with
  | zero => exact ⟨_,_,Nat.zero_le _,Good.a [true] 4,entry v⟩
  | succ n ih =>
    obtain ⟨k,z,hk,hz,hr⟩ := ih
    obtain ⟨t,z',ht,hz',he⟩ := next v hz
    exact ⟨k+t,z',by omega,hz',join0 hr he⟩

theorem never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,_,hr⟩ := live v n
  have hz : (BB6Coverage.Agent50Zipper.zrun (table v) t start).map project = some z :=
    (run_project (table v) t start).trans hr
  cases h : BB6Coverage.Agent50Zipper.zrun (table v) t start with
  | none => simp [h] at hz
  | some z =>
    have H := BB6Coverage.Agent50Zipper.zrun_sound (table v) m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms next
#print axioms never
end BB6.Agent11Raw391LEBinarySix
