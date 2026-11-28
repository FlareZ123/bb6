import SweepPumping
import FastFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13Coupled6RFCounter
open BB6Coverage BB6Coverage.Agent31Pump

inductive Variant | zLD | oLD | oRC
  deriving DecidableEq

def fcode : Variant → Nat | .zLD => 12 | .oLD => 14 | .oRC => 11
def p (v : Variant) : PartialMachine := FAR.fromCodes [7,14,11,12,2,19,5,0,7,21,fcode v,24]
def entry : Variant → Nat | .zLD => 235 | .oLD => 247 | .oRC => 223
def preCost : Variant → Nat | .zLD => 68 | .oLD => 74 | .oRC => 62
def carryCost : Variant → Nat | .zLD => 16 | .oLD => 18 | .oRC => 14
def secondCost : Variant → Nat | .zLD => 23 | .oLD => 25 | .oRC => 21
abbrev A (l r : List Bool) : Z0 := ⟨0,l,r⟩
abbrev B (l r : List Bool) : Z0 := ⟨1,l,r⟩
abbrev U : List Bool := [true,true]
abbrev Y : List Bool := [false,true]
abbrev D0 : List Bool := [false,true,false,true,false,true]
abbrev D1 : List Bool := [true,true,false,true,false,true]
abbrev P : List Bool := [false,true,false,true,false,true,false,true,false,true,false,false]
abbrev Q : List Bool := [true,false,false]
abbrev marker : List Bool := [false,true,true,true,true,true,true,true,true,false]
abbrev ones (n : Nat) : List Bool := List.replicate n true
abbrev leftB (n : Nat) : List Bool := false::(ones n ++ marker)

def enc : List Bool → List Bool
  | [] => [true]
  | b::bs => (if b then D1 else D0) ++ enc bs

def root (second : Bool) (bs : List Bool) : Z0 :=
  if second then B (leftB 3) (Q++enc bs) else A [true,false] (P++enc bs)

def next (second : Bool) (k : Nat) : List Bool → Bool × List Bool
  | [] => if second then (false,List.replicate (k+1) false) else (true,List.replicate k false)
  | false::bs => (second,List.replicate k false ++ true::bs)
  | true::bs => next second (k+1) bs

theorem rep_add (w : List Bool) (m n : Nat) : rep w (m+n) = rep w m ++ rep w n := by
  induction m with
  | zero => simp [rep]
  | succ m ih => rw [Nat.succ_add,rep,ih,rep]; simp only [List.append_assoc]

theorem replicate_append (a : Bool) (m n : Nat) : List.replicate (m+n) a = List.replicate m a ++ List.replicate n a := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_add,List.replicate_succ,ih,List.replicate_succ]; rfl

theorem ones_add (m n : Nat) : ones (m+n) = ones m ++ ones n := replicate_append true m n

theorem ones_rep (n : Nat) : rep U n = ones (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep,ih,show 2*(n+1)=2+2*n by omega,ones_add]
    rfl

theorem d0_rep (n : Nat) : rep Y (3*n) = rep D0 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 3*(n+1)=3+3*n by omega,rep_add,ih,rep]
    rfl

theorem enc_zeros (k : Nat) (bs : List Bool) :
    enc (List.replicate k false ++ bs) = rep D0 k ++ enc bs := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ,enc,rep,ih]

theorem enc_zero_end (k : Nat) : enc (List.replicate k false) = rep D0 k ++ [true] := by
  have h := enc_zeros k []
  simpa only [List.append_nil,enc] using h

theorem init (v : Variant) : run0 (p v) (entry v) (A [] []) = some (root false []) := by cases v <;> rfl

theorem primaryPrefix (v : Variant) (R : List Bool) :
    run0 (p v) (preCost v) (A [true,false] (P++R)) = some (B (leftB 3) R) := by cases v <;> rfl

theorem secondaryPrefix (v : Variant) (L R : List Bool) :
    run0 (p v) 3 (B (false::L) (Q++R)) = some (B (false::(ones 3++L)) R) := by cases v <;> rfl

theorem carry (v : Variant) (L R : List Bool) :
    run0 (p v) (carryCost v) (B (false::L) (D1++R)) = some (B (false::(ones 6++L)) R) := by cases v <;> rfl

theorem zeroDigit (v : Variant) (L R : List Bool) :
    run0 (p v) 2 (B (false::L) (D0++R)) = some (A (true::L) (D1++R)) := by cases v <;> rfl

theorem terminal (v : Variant) (L : List Bool) :
    run0 (p v) 5 (B (false::L) [true]) = some (A (ones 4++L) [true]) := by cases v <;> rfl

theorem pair (v : Variant) (L R : List Bool) :
    run0 (p v) 2 (A (U++L) R) = some (A L (Y++R)) := by cases v <;> rfl

theorem sweep (v : Variant) (n : Nat) (L R : List Bool) :
    run0 (p v) (2*n) (A (ones (2*n)++L) R) = some (A L (rep Y n++R)) := by
  rw [← ones_rep]
  simpa only [List.nil_append] using sweepL (p v) 0 [] [] U Y 2 (by intro L R; exact pair v L R) n L R

theorem primaryFinish (v : Variant) (R : List Bool) :
    run0 (p v) 16 (A marker (rep Y 2++R)) = some (A [true,false] (P++R)) := by cases v <;> rfl

theorem secondaryFinish (v : Variant) (R : List Bool) :
    run0 (p v) (secondCost v) (A (true::marker) (rep Y 3++R)) = some (B (leftB 3) (Q++R)) := by cases v <;> rfl

def nLeft (second : Bool) (k : Nat) := (if second then 6 else 3)+6*k

def scanRoot (second : Bool) (k : Nat) (bs : List Bool) : Z0 := B (leftB (nLeft second k)) (enc bs)

theorem carryOne (v : Variant) (second : Bool) (k : Nat) (bs : List Bool) :
    run0 (p v) (carryCost v) (scanRoot second k (true::bs)) = some (scanRoot second (k+1) bs) := by
  have h := carry v (ones (nLeft second k)++marker) (enc bs)
  have hn : nLeft second (k+1)=6+nLeft second k := by simp [nLeft]; omega
  simpa only [scanRoot,leftB,enc,ite_true,hn,ones_add,List.append_assoc,List.singleton_append] using h

theorem enter (v : Variant) (second : Bool) (bs : List Bool) :
    ∃ t, 0<t ∧ run0 (p v) t (root second bs) = some (scanRoot second 0 bs) := by
  cases second
  · refine ⟨preCost v,?_,?_⟩
    · cases v <;> decide
    · exact primaryPrefix v (enc bs)
  · exact ⟨3,by decide,secondaryPrefix v (ones 3++marker) (enc bs)⟩

theorem zeroPrimary (v : Variant) (k : Nat) (bs : List Bool) :
    ∃ t, 0<t ∧ run0 (p v) t (scanRoot false k (false::bs)) = some (root false (List.replicate k false ++ true::bs)) := by
  have h := zeroDigit v (ones (nLeft false k)++marker) (enc bs)
  have hl : true::(ones (nLeft false k)++marker) = ones (2*(2+3*k))++marker := by
    rw [show 2*(2+3*k)=1+nLeft false k by simp [nLeft]; omega,ones_add]
    simp only [List.append_assoc]
    rfl
  rw [hl] at h
  have h2 := sweep v (2+3*k) marker (D1++enc bs)
  have h3 := primaryFinish v (rep D0 k++D1++enc bs)
  rw [rep_add,d0_rep] at h2
  simp only [List.append_assoc] at h2 h3
  have j := join0 h h2
  have j' := join0 j h3
  refine ⟨2+2*(2+3*k)+16,by omega,?_⟩
  simpa only [scanRoot,root,ite_false,leftB,enc,enc_zeros,List.append_assoc,List.singleton_append,ite_true,Bool.false_eq_true] using j'

theorem zeroSecondary (v : Variant) (k : Nat) (bs : List Bool) :
    ∃ t, 0<t ∧ run0 (p v) t (scanRoot true k (false::bs)) = some (root true (List.replicate k false ++ true::bs)) := by
  have h := zeroDigit v (ones (nLeft true k)++marker) (enc bs)
  have hl : true::(ones (nLeft true k)++marker) = ones (2*(3+3*k))++(true::marker) := by
    rw [show nLeft true k=2*(3+3*k) by simp [nLeft]; omega]
    change ones (2*(3+3*k)+1)++marker = _
    rw [ones_add]
    simp only [List.append_assoc]
    rfl
  rw [hl] at h
  have h2 := sweep v (3+3*k) (true::marker) (D1++enc bs)
  have h3 := secondaryFinish v (rep D0 k++D1++enc bs)
  rw [rep_add,d0_rep] at h2
  simp only [List.append_assoc] at h2 h3
  have j := join0 h h2
  have j' := join0 j h3
  refine ⟨2+2*(3+3*k)+secondCost v,by omega,?_⟩
  simpa only [scanRoot,root,ite_true,leftB,enc,enc_zeros,List.append_assoc,List.singleton_append,ite_false,Bool.false_eq_true] using j'

theorem endPrimary (v : Variant) (k : Nat) :
    ∃ t, 0<t ∧ run0 (p v) t (scanRoot false k []) = some (root true (List.replicate k false)) := by
  have h := terminal v (ones (nLeft false k)++marker)
  have hl : ones 4++(ones (nLeft false k)++marker) = ones (2*(3+3*k))++(true::marker) := by
    rw [← List.append_assoc,← ones_add,show 4+nLeft false k=2*(3+3*k)+1 by simp [nLeft]; omega,ones_add]
    simp only [List.append_assoc]
    rfl
  rw [hl] at h
  have h2 := sweep v (3+3*k) (true::marker) [true]
  have h3 := secondaryFinish v (rep D0 k++[true])
  rw [rep_add,d0_rep] at h2
  simp only [List.append_assoc] at h2 h3
  have j := join0 h h2
  have j' := join0 j h3
  refine ⟨5+2*(3+3*k)+secondCost v,by omega,?_⟩
  simpa only [scanRoot,root,ite_true,leftB,enc,enc_zero_end,List.append_assoc,List.singleton_append] using j'

theorem endSecondary (v : Variant) (k : Nat) :
    ∃ t, 0<t ∧ run0 (p v) t (scanRoot true k []) = some (root false (List.replicate (k+1) false)) := by
  have h := terminal v (ones (nLeft true k)++marker)
  have hl : ones 4++(ones (nLeft true k)++marker) = ones (2*(5+3*k))++marker := by
    rw [← List.append_assoc,← ones_add,show 4+nLeft true k=2*(5+3*k) by simp [nLeft]; omega]
  rw [hl] at h
  have h3 := primaryFinish v (rep D0 (k+1)++[true])
  have h2' := sweep v (2+3*(k+1)) marker [true]
  rw [rep_add,d0_rep] at h2'
  have h2 : run0 (p v) (2*(5+3*k)) (A (ones (2*(5+3*k))++marker) [true]) = some (A marker (rep Y 2++rep D0 (k+1)++[true])) := by
    simpa only [show 2+3*(k+1)=5+3*k by omega] using h2'
  simp only [List.append_assoc] at h2 h3
  have j := join0 h h2
  have j' := join0 j h3
  refine ⟨5+2*(5+3*k)+16,by omega,?_⟩
  simpa only [scanRoot,root,ite_false,leftB,enc,enc_zero_end,List.append_assoc,List.singleton_append,Bool.false_eq_true] using j'

theorem scan (v : Variant) (second : Bool) (k : Nat) (bs : List Bool) :
    ∃ t, 0<t ∧ run0 (p v) t (scanRoot second k bs) = some (root (next second k bs).1 (next second k bs).2) := by
  induction bs generalizing k with
  | nil => cases second
           · exact endPrimary v k
           · exact endSecondary v k
  | cons b bs ih =>
    cases b
    · cases second
      · exact zeroPrimary v k bs
      · exact zeroSecondary v k bs
    · obtain ⟨t,ht,hr⟩ := ih (k+1)
      exact ⟨carryCost v+t,by omega,join0 (carryOne v second k bs) hr⟩

theorem growth (v : Variant) (second : Bool) (bs : List Bool) :
    ∃ t, 0<t ∧ run0 (p v) t (root second bs) = some (root (next second 0 bs).1 (next second 0 bs).2) := by
  obtain ⟨t,ht,hr⟩ := enter v second bs
  obtain ⟨u,hu,hs⟩ := scan v second 0 bs
  exact ⟨t+u,by omega,join0 hr hs⟩

def trajectory : Nat → Bool × List Bool
  | 0 => (false,[])
  | n+1 => next (trajectory n).1 0 (trajectory n).2

def family (n : Nat) := root (trajectory n).1 (trajectory n).2

theorem live (v : Variant) (n : Nat) : ∃ t, n ≤ t ∧ run0 (p v) t (A [] []) = some (family n) := by
  induction n with
  | zero => exact ⟨entry v,by omega,init v⟩
  | succ n ih =>
    obtain ⟨t,ht,hr⟩ := ih
    obtain ⟨u,hu,hs⟩ := growth v (trajectory n).1 (trajectory n).2
    exact ⟨t+u,by omega,join0 hr hs⟩

theorem never (v : Variant) (m : Machine) (hm : compatible (p v) m) : NeverHalts m := by
  let cost := fun n => Classical.choose (growth v (trajectory n).1 (trajectory n).2)
  exact never_of_growth (p v) family (entry v) cost (init v)
    (fun n => (Classical.choose_spec (growth v (trajectory n).1 (trajectory n).2)).1)
    (fun n => (Classical.choose_spec (growth v (trajectory n).1 (trajectory n).2)).2) m hm

#print axioms never
#print axioms init
#print axioms growth
#print axioms live
end BB6.Agent46Raw13Coupled6RFCounter
