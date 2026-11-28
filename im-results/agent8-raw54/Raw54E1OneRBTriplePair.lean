import SweepPumping

/-! The 295/332 one-hole tables share a finite-word invariant. The third
    symbol of each right block is the next scanned symbol after a three-step
    advance. No restriction is needed on the first or third block symbol. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option autoImplicit false
namespace BB6.Agent8Raw54.E1OneRB.TriplePair
open BB6Coverage BB6Coverage.Agent31Pump

def table (v : Bool) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => if v then some (some ⟨true,false,4⟩) else some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,true => some (some ⟨true,true,1⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

abbrev P : List Bool := [true,true,true]
abbrev O (k : Nat) := rep P k
abbrev A (b : Bool) (k : Nat) (R : List Bool) : Z0 := ⟨0,[b,true,true]++O k++[false],R⟩
abbrev extra (v : Bool) : Nat := if v then 2 else 0

private theorem commute (k : Nat) : [true,true] ++ O k = O k ++ [true,true] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rep,List.append_assoc]
    change true::true::true::([true,true]++O k) = true::true::true::(O k++[true,true])
    rw [ih]

private theorem trueBase (v : Bool) (R : List Bool) :
    run0 (table v) (8+extra v) (A true 0 R) = some (A false 0 R) := by
  cases v <;> rfl

private theorem trueMore (v : Bool) (k : Nat) (R : List Bool) :
    run0 (table v) (3*k+11+extra v) (A true (k+1) R) =
      some (A true 0 (O k++[true,true,false]++R)) := by
  have h1 : run0 (table v) (1+extra v) (A true (k+1) R) =
      some (⟨5,[true,true,true,true,true]++O k++[false],false::R⟩ : Z0) := by
    cases v <;> rfl
  have h2 : run0 (table v) (3*k) ⟨5,[true,true,true,true,true]++O k++[false],false::R⟩ =
      some ⟨5,[true,true,true,true,true,false],O k++(false::R)⟩ := by
    exact (sweepL (table v) 5 [true,true,true,true,true] [] P P 3
        (fun L R => by cases v <;> rfl) k [false] (false::R))
  have h3 : run0 (table v) 10 ⟨5,[true,true,true,true,true,false],O k++(false::R)⟩ =
      some (A true 0 ([true,true]++O k++(false::R))) := by
    cases v <;> rfl
  have h := join0 (join0 h1 h2) h3
  rw [show 1+extra v+3*k+10 = 3*k+11+extra v by omega] at h
  rw [commute] at h
  simpa only [List.append_assoc,List.cons_append,List.nil_append] using h

private theorem zeroOne (v : Bool) (k : Nat) (R : List Bool) :
    run0 (table v) (3*k+10) (A false k (true::R)) =
      some (A true 0 (O k++(false::R))) := by
  have h1 : run0 (table v) 2 (A false k (true::R)) =
      some (⟨5,P++O k++[false],false::R⟩ : Z0) := by
    cases v <;> rfl
  have h2 : run0 (table v) (3*k) ⟨5,P++O k++[false],false::R⟩ =
      some ⟨5,[true,true,true,false],O k++(false::R)⟩ := by
    exact (sweepL (table v) 5 P [] P P 3 (fun L R => by cases v <;> rfl) k [false] (false::R))
  have h3 : run0 (table v) 8 ⟨5,[true,true,true,false],O k++(false::R)⟩ =
      some (A true 0 (O k++(false::R))) := by
    cases v <;> rfl
  have h := join0 (join0 h1 h2) h3
  simpa only [show 2+3*k+8=3*k+10 by omega] using h

private theorem zeroZero (v b : Bool) (k : Nat) (R : List Bool) :
    run0 (table v) 3 (A false k (false::true::b::R)) = some (A b (k+1) R) := by
  cases v <;> cases b <;> rfl

private theorem zeroNil (v : Bool) (k : Nat) :
    run0 (table v) 9 (A false k []) = some (A true (k+1) []) := by
  cases v <;> rfl

abbrev Digit := Bool × Bool
def word : List Digit → List Bool
  | [] => []
  | (b,c)::w => b::true::c::word w

private theorem word_ones (k : Nat) (w : List Digit) :
    word (List.replicate k (true,true) ++ w) = O k ++ word w := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ,List.cons_append,word,rep,ih]; rfl

structure Section where
  bit : Bool
  count : Nat
  digits : List Digit

def config (s : Section) : Z0 := A s.bit s.count (word s.digits)

def advance : Section → Section
  | ⟨true,0,w⟩ => ⟨false,0,w⟩
  | ⟨true,k+1,w⟩ => ⟨true,0,List.replicate k (true,true) ++ (true,false)::w⟩
  | ⟨false,k,[]⟩ => ⟨true,k+1,[]⟩
  | ⟨false,k,(false,c)::w⟩ => ⟨c,k+1,w⟩
  | ⟨false,k,(true,c)::w⟩ => ⟨true,0,List.replicate k (true,true) ++ (false,c)::w⟩

def duration (v : Bool) : Section → Nat
  | ⟨true,0,_⟩ => 8+extra v
  | ⟨true,k+1,_⟩ => 3*k+11+extra v
  | ⟨false,_,[]⟩ => 9
  | ⟨false,_,(false,_)::_⟩ => 3
  | ⟨false,k,(true,_)::_⟩ => 3*k+10

theorem positive (v : Bool) (s : Section) : 0 < duration v s := by
  obtain ⟨b,k,w⟩ := s
  cases b with
  | false => cases w with
    | nil => simp [duration]
    | cons d w => obtain ⟨b,c⟩ := d; cases b <;> simp [duration] <;> omega
  | true => cases k <;> simp [duration] <;> omega

theorem closed (v : Bool) (s : Section) :
    run0 (table v) (duration v s) (config s) = some (config (advance s)) := by
  obtain ⟨b,k,w⟩ := s
  cases b with
  | true => cases k with
    | zero => exact trueBase v (word w)
    | succ k => simpa only [duration,config,advance,word_ones,word,List.append_assoc,List.cons_append,List.nil_append] using trueMore v k (word w)
  | false => cases w with
    | nil => exact zeroNil v k
    | cons d w => obtain ⟨b,c⟩ := d; cases b with
      | false => exact zeroZero v c k (word w)
      | true => simpa only [duration,config,advance,word_ones,word,List.append_assoc] using zeroOne v k (true::c::word w)

def orbit : Nat → Section
  | 0 => ⟨true,1,[]⟩
  | n+1 => advance (orbit n)

def entryTime (v : Bool) : Nat := if v then 39 else 35

theorem entry (v : Bool) : run0 (table v) (entryTime v) ⟨0,[],[]⟩ = some (config (orbit 0)) := by
  cases v <;> rfl

theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) (fun n => config (orbit n)) (entryTime v) (fun n => duration v (orbit n))
    (entry v) (fun n => positive v (orbit n)) (fun n => closed v (orbit n)) m hm

#print axioms closed
#print axioms never
end BB6.Agent8Raw54.E1OneRB.TriplePair
