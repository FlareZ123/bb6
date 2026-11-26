import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent40Raw57Binary
open BB6Coverage BB6Coverage.Agent31Pump

def table (v : Bool) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨v,true,if v then 2 else 4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | _,_ => none
abbrev z : Bool := false
abbrev o : Bool := true
abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev C (L R : List Bool) : Z0 := ⟨2,L,R⟩
inductive Word where
  | nil | term | zero (tail : Word) | one (tail : Word)
  deriving DecidableEq

def encode : Word → List Bool
  | .nil => []
  | .term => [z,o]
  | .zero w => [z,o,o,z,o,o] ++ encode w
  | .one w => [z,o,z,z,o,o] ++ encode w

def inc : Word → Word
  | .nil => .term
  | .term => .zero .nil
  | .zero w => .one w
  | .one w => .zero (inc w)

def cCost (v : Bool) : Nat := if v then 6 else 8
def cost (v : Bool) : Word → Nat
  | .nil => 5
  | .term => 15
  | .zero _ => 7
  | .one w => cCost v + cost v w + 10

theorem carry (v : Bool) (L : List Bool) (w : Word) :
    run0 (table v) (cCost v) (C (z::L) ([o,z,z,o,o]++encode w)) =
      some (C ([z,o,o,z,o,o,z]++L) (encode w).tail) := by
  cases v <;> cases w <;> rfl

theorem ret (v : Bool) (L R : List Bool) :
    run0 (table v) 5 (A ([o,o,z]++L) R) = some (A L ([z,o,o]++R)) := by
  cases v <;> rfl

theorem process (v : Bool) (w : Word) (L : List Bool) :
    run0 (table v) (cost v w) (C (z::o::L) (encode w).tail) = some (A (o::L) (encode (inc w))) := by
  induction w generalizing L with
  | nil => cases v <;> rfl
  | term => cases v <;> rfl
  | zero w => cases v <;> rfl
  | one w ih =>
    have h1 := carry v (o::L) w
    have h2 := ih ([o,z,o,o,z,o]++L)
    have h3 := ret v ([o,o,z,o]++L) (encode (inc w))
    have h4 := ret v (o::L) ([z,o,o]++encode (inc w))
    have h := join0 (join0 (join0 h1 h2) h3) h4
    simpa only [cost,encode,inc,List.append_assoc,List.cons_append,List.tail_cons,Nat.add_assoc,List.nil_append] using h

abbrev P : List Bool := [o,o]
def sect (n : Nat) (w : Word) : Z0 := A [] (rep P (n+1)++encode w)

theorem prepare (v : Bool) (R : List Bool) :
    run0 (table v) 3 (A [] (P++R)) = some (A [] ([z]++P++R)) := by cases v <;> rfl

theorem firstScan (R : List Bool) :
    run0 (table false) 4 (A [] ([z]++P++R)) = some (A ([z]++P) (z::R)) := by rfl

theorem scanOne (L R : List Bool) :
    run0 (table false) 4 (A ([z]++L) ([z]++P++R)) = some (A ([z]++P++L) (z::R)) := by rfl

theorem scan (n : Nat) (w : Word) :
    run0 (table false) (3+4+4*n) (sect n w) = some (A ([z]++rep P (n+1)) (z::encode w)) := by
  have h1 := prepare false (rep P n++encode w)
  have h2 := firstScan (rep P n++encode w)
  have h3 := sweepR (table false) 0 [z] [z] P P 4
    (fun L R => by simpa only [List.append_assoc,List.cons_append,List.nil_append] using scanOne L R) n P (encode w)
  have h := join0 (join0 h1 h2) h3
  simpa only [sect,rep,List.append_assoc,rep_snoc,List.cons_append,List.nil_append] using h

theorem startProcess (v : Bool) (L : List Bool) (w : Word) :
    run0 (table v) 2 (A (z::L) (z::encode w)) = some (C ([z]++P++L) (encode w).tail) := by
  cases v <;> cases w <;> rfl

theorem drainOne (v : Bool) (L R : List Bool) :
    run0 (table v) 2 (A (P++L) R) = some (A L (P++R)) := by cases v <;> rfl

theorem drain (v : Bool) (n : Nat) (R : List Bool) :
    run0 (table v) (2*n) (A (rep P n) R) = some (A [] (rep P n++R)) := by
  have h := sweepL (table v) 0 [] [] P P 2 (fun L R => by simpa using drainOne v L R) n [] R
  simpa using h

theorem trueFirst (R : List Bool) :
    run0 (table true) 2 (A [] ([z]++P++R)) = some (C [o,o,o] (o::R)) := by rfl

theorem truePair (L R : List Bool) :
    run0 (table true) 2 (C (o::L) (P++R)) = some (C (o::(P++L)) R) := by rfl

theorem trueEnd (L : List Bool) (w : Word) :
    run0 (table true) 2 (C (o::L) (o::encode w)) = some (C (z::o::o::L) (encode w).tail) := by
  cases w <;> rfl

theorem oneComm (n : Nat) : o::rep P n = rep P n++[o] := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,List.append_assoc,List.cons_append,List.nil_append]; exact congrArg (fun L => o::o::L) ih

theorem trueScan (n : Nat) (w : Word) :
    run0 (table true) (3+2+2*n+2) (sect n w) = some (C (z::rep P (n+2)) (encode w).tail) := by
  have h1 := prepare true (rep P n++encode w)
  have h2 := trueFirst (rep P n++encode w)
  have h3 := sweepR (table true) 2 [o] [] P P 2
    (fun L R => by simpa only [List.append_assoc,List.nil_append,List.cons_append] using truePair L R) n P (o::encode w)
  have h4 := trueEnd (rep P n++P) w
  have h12 := join0 h1 h2
  rw [← List.cons_append,oneComm n,List.append_assoc] at h12
  have h123 := join0 h12 h3
  have h := join0 h123 h4
  simpa only [sect,rep,List.append_assoc,List.nil_append,List.cons_append,rep_snoc] using h

theorem processPairs (v : Bool) (n : Nat) (w : Word) :
    run0 (table v) (cost v w) (C (z::rep P (n+1)) (encode w).tail) = some (A (rep P (n+1)) (encode (inc w))) := by
  exact process v w (o::rep P n)

def epochCost (v : Bool) (n : Nat) (w : Word) : Nat :=
  (if v then 3+2+2*n+2 else 3+4+4*n+2) + cost v w + 2*(n+2)

theorem epoch (v : Bool) (n : Nat) (w : Word) :
    run0 (table v) (epochCost v n w) (sect n w) = some (sect (n+1) (inc w)) := by
  cases v with
  | false =>
    have h12 := join0 (scan n w) (startProcess false (rep P (n+1)) w)
    exact join0 (join0 h12 (processPairs false (n+1) w)) (drain false (n+2) (encode (inc w)))
  | true =>
    exact join0 (join0 (trueScan n w) (processPairs true (n+1) w)) (drain true (n+2) (encode (inc w)))

def wordAt : Nat → Word
  | 0 => .term
  | n+1 => inc (wordAt n)

theorem entry (v : Bool) : run0 (table v) 9 ⟨0,[],[]⟩ = some (sect 0 .term) := by cases v <;> rfl

theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) (fun k => sect k (wordAt k)) 9 (fun k => epochCost v k (wordAt k))
    (entry v) (by intro k; unfold epochCost; cases v <;> simp <;> omega) (fun k => epoch v k (wordAt k)) m hm

#print axioms epoch
#print axioms never
end BB6Coverage.Agent40Raw57Binary

namespace BB6Coverage.Agent40Raw57Binary.M2021
open BB6Coverage
abbrev table := Agent40Raw57Binary.table false
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent40Raw57Binary.never false m hm
#print axioms never
end BB6Coverage.Agent40Raw57Binary.M2021

namespace BB6Coverage.Agent40Raw57Binary.M2172
open BB6Coverage
abbrev table := Agent40Raw57Binary.table true
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent40Raw57Binary.never true m hm
#print axioms never
end BB6Coverage.Agent40Raw57Binary.M2172
