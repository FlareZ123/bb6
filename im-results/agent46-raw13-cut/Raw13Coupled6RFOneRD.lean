import SweepPumping
import FastFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13Coupled6RFOneRD
open BB6Coverage BB6Coverage.Agent31Pump

def p : PartialMachine := FAR.fromCodes [7,14,11,12,2,19,5,0,7,21,15,24]
abbrev A (l r : List Bool) : Z0 := ⟨0,l,r⟩
abbrev B (l r : List Bool) : Z0 := ⟨1,l,r⟩
abbrev E (l r : List Bool) : Z0 := ⟨4,l,r⟩
abbrev P : List Bool := [true,false]
abbrev Q : List Bool := [false,true,false,true,false]
abbrev U : List Bool := [true,true]
abbrev Y : List Bool := [false,true]
abbrev D0 : List Bool := [true,false,true,false,true,false]
abbrev D1 : List Bool := [true,true,true,false,true,false]
abbrev fin : List Bool := [true,true]
abbrev left0 : List Bool := [false,true,true,true,false,true,true,true,true,true,false,true,true,false,true,true,false]
abbrev left1 : List Bool := [true,false,true,true,false,true,true,true,true,true,false,true,true,false,true,true,false]
abbrev W : List Bool := [false,true,true,false,true,true,true,true,true,false,true,true,false,true,true,false]
abbrev frame : List Bool := [false,true,true,false]
abbrev ones (n : Nat) : List Bool := List.replicate n true
abbrev tail1 : List Bool := [true,true,false,true,false]

def enc : List Bool → List Bool
  | [] => fin
  | b::bs => (if b then D1 else D0) ++ enc bs

def root (second : Bool) (bs : List Bool) : Z0 :=
  if second then B left1 (Q++enc bs) else B left0 (P++enc bs)

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
  | succ n ih => rw [rep,ih,show 2*(n+1)=2+2*n by omega,ones_add]; rfl

theorem d0_rep (n : Nat) : rep P (3*n) = rep D0 n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show 3*(n+1)=3+3*n by omega,rep_add,ih,rep]; rfl

theorem enc_zeros (k : Nat) (bs : List Bool) :
    enc (List.replicate k false ++ bs) = rep D0 k ++ enc bs := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ,enc,rep,ih]

theorem enc_zero_end (k : Nat) : enc (List.replicate k false) = rep D0 k ++ fin := by
  have h := enc_zeros k []
  simpa only [List.append_nil,enc] using h

-- A paired left sweep converts two ones into the right-hand block 01.
theorem pair (L R : List Bool) : run0 p 2 (A (U++L) R) = some (A L (Y++R)) := rfl
theorem sweep (n : Nat) (L R : List Bool) : run0 p (2*n) (A (ones (2*n)++L) R) = some (A L (rep Y n++R)) := by
  rw [←ones_rep]
  simpa only [List.nil_append] using sweepL p 0 [] [] U Y 2 (by intro L R; exact pair L R) n L R

theorem finishPrimary (R : List Bool) : run0 p 1 (A W (false::R)) = some (B left0 R) := rfl
theorem finishSecondary (R : List Bool) : run0 p 2 (A (true::W) R) = some (B left1 R) := rfl

-- The carry loop keeps all unscanned tape intact.
theorem carry (L R : List Bool) :
    run0 p 26 (E (frame++L) (D1++R)) = some (E (frame++ones 6++L) R) := rfl
theorem zeroDigit (L R : List Bool) :
    run0 p 11 (E (frame++L) (D0++R)) = some (A (ones 5++L) (tail1++R)) := rfl
theorem terminal (L : List Bool) :
    run0 p 14 (E (frame++L) fin) = some (A (ones 8++L) [true]) := rfl

-- First digit, before the common positive-length carry frame.
theorem firstZero0 (R : List Bool) :
    run0 p 44 (B left0 (P++D0++R)) = some (B left0 (P++D1++R)) := rfl
theorem firstZero1 (R : List Bool) :
    run0 p 44 (B left1 (Q++D0++R)) = some (B left1 (Q++D1++R)) := rfl
theorem firstEnd0 : run0 p 100 (root false []) = some (root false [false]) := rfl
theorem firstEnd1 : run0 p 50 (root true []) = some (root false [false]) := rfl

def count (second : Bool) (k : Nat) := (if second then 8 else 5)+6*k

def scanRoot (second : Bool) (k : Nat) (bs : List Bool) : Z0 :=
  E (frame++ones (count second k)++W) (enc bs)

theorem firstCarry0 (bs : List Bool) :
    run0 p 54 (root false (true::bs)) = some (scanRoot false 0 bs) := rfl
theorem firstCarry1 (bs : List Bool) :
    run0 p 51 (root true (true::bs)) = some (scanRoot true 0 bs) := rfl

theorem carryOne (second : Bool) (k : Nat) (bs : List Bool) :
    run0 p 26 (scanRoot second k (true::bs)) = some (scanRoot second (k+1) bs) := by
  have h := carry (ones (count second k)++W) (enc bs)
  have hc : count second (k+1)=6+count second k := by simp [count]; omega
  simpa only [scanRoot,enc,ite_true,hc,ones_add,List.append_assoc] using h

-- Rotate alternating blocks across the last one of the right-hand frame.
theorem rotateY (n : Nat) : true :: rep Y n = rep P n ++ [true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change P ++ (true::rep Y n) = P ++ rep P n ++ [true]
    rw [ih,List.append_assoc]

theorem firstRight (n : Nat) (R : List Bool) :
    rep Y (n+1)++R = false :: (rep P n++true::R) := by
  change false::((true::rep Y n)++R) = _
  rw [rotateY,List.append_assoc]
  rfl

theorem primaryDigits (k : Nat) (R : List Bool) :
    rep Y (5+3*k)++tail1++R = false::(P++rep D0 (k+1)++D1++R) := by
  have h : 5+3*k=(1+3*(k+1))+1 := by omega
  rw [h,List.append_assoc,firstRight,rep_add,d0_rep]
  simp only [List.append_assoc]
  rfl

theorem secondaryDigits (k : Nat) (R : List Bool) :
    rep Y (6+3*k)++tail1++R = Q++rep D0 (k+1)++D1++R := by
  rw [show 6+3*k=2+(3*(k+1)+1) by omega,rep_add,List.append_assoc,List.append_assoc (rep Y 2)]
  rw [firstRight (3*(k+1)),d0_rep]
  simp only [List.append_assoc]
  rfl

theorem primaryEndDigits (k : Nat) :
    rep Y (8+3*k)++[true] = false::(P++rep D0 (k+2)++fin) := by
  rw [show 8+3*k=(1+3*(k+2))+1 by omega,firstRight,rep_add,d0_rep]
  rfl

theorem secondaryEndDigits (k : Nat) :
    rep Y (6+3*k)++[true] = Q++rep D0 (k+1)++fin := by
  rw [show 6+3*k=2+(3*(k+1)+1) by omega,rep_add,List.append_assoc,firstRight (3*(k+1)),d0_rep]
  simp only [List.append_assoc]
  rfl

-- On digit0, erase all carried digit1 blocks and set the next digit to digit1.
theorem zeroPrimary (k : Nat) (bs : List Bool) : ∃ t, 0<t ∧
    run0 p t (scanRoot false k (false::bs)) = some (root false (List.replicate (k+1) false ++ true::bs)) := by
  have h := zeroDigit (ones (count false k)++W) (enc bs)
  have he : ones 5++(ones (count false k)++W) = ones (2*(5+3*k))++W := by
    rw [←List.append_assoc,←ones_add]; congr 2; simp [count]; omega
  rw [he] at h
  have j := join0 h (sweep (5+3*k) W (tail1++enc bs))
  have j' : run0 p (11+2*(5+3*k)) (E (frame++(ones (count false k)++W)) (D0++enc bs)) = some (A W (false::(P++rep D0 (k+1)++D1++enc bs))) := by
    simpa only [←List.append_assoc,primaryDigits] using j
  have z := join0 j' (finishPrimary (P++rep D0 (k+1)++D1++enc bs))
  refine ⟨11+2*(5+3*k)+1,by omega,?_⟩
  simpa only [scanRoot,root,ite_false,Bool.false_eq_true,enc,enc_zeros,List.append_assoc,ite_true] using z

theorem zeroSecondary (k : Nat) (bs : List Bool) : ∃ t, 0<t ∧
    run0 p t (scanRoot true k (false::bs)) = some (root true (List.replicate (k+1) false ++ true::bs)) := by
  have h := zeroDigit (ones (count true k)++W) (enc bs)
  have he : ones 5++(ones (count true k)++W) = ones (2*(6+3*k))++(true::W) := by
    rw [←List.append_assoc,←ones_add,show 5+count true k=2*(6+3*k)+1 by simp [count]; omega,ones_add,List.append_assoc]
    rfl
  rw [he] at h
  have j := join0 h (sweep (6+3*k) (true::W) (tail1++enc bs))
  have j' : run0 p (11+2*(6+3*k)) (E (frame++(ones (count true k)++W)) (D0++enc bs)) = some (A (true::W) (Q++rep D0 (k+1)++D1++enc bs)) := by
    simpa only [←List.append_assoc,secondaryDigits] using j
  have z := join0 j' (finishSecondary (Q++rep D0 (k+1)++D1++enc bs))
  refine ⟨11+2*(6+3*k)+2,by omega,?_⟩
  simpa only [scanRoot,root,ite_true,Bool.false_eq_true,enc,enc_zeros,List.append_assoc,ite_false] using z

-- Overflow changes phase; the secondary overflow increases the digit width.
theorem endPrimary (k : Nat) : ∃ t, 0<t ∧
    run0 p t (scanRoot false k []) = some (root true (List.replicate (k+1) false)) := by
  have h := terminal (ones (count false k)++W)
  have he : ones 8++(ones (count false k)++W) = ones (2*(6+3*k))++(true::W) := by
    rw [←List.append_assoc,←ones_add,show 8+count false k=2*(6+3*k)+1 by simp [count]; omega,ones_add,List.append_assoc]
    rfl
  rw [he] at h
  have j := join0 h (sweep (6+3*k) (true::W) [true])
  rw [secondaryEndDigits] at j
  have z := join0 j (finishSecondary (Q++rep D0 (k+1)++fin))
  refine ⟨14+2*(6+3*k)+2,by omega,?_⟩
  simpa only [scanRoot,root,ite_true,enc,enc_zero_end,List.append_assoc] using z

theorem endSecondary (k : Nat) : ∃ t, 0<t ∧
    run0 p t (scanRoot true k []) = some (root false (List.replicate (k+2) false)) := by
  have h := terminal (ones (count true k)++W)
  have he : ones 8++(ones (count true k)++W) = ones (2*(8+3*k))++W := by
    rw [←List.append_assoc,←ones_add]; congr 2; simp [count]; omega
  rw [he] at h
  have j := join0 h (sweep (8+3*k) W [true])
  rw [primaryEndDigits] at j
  have z := join0 j (finishPrimary (P++rep D0 (k+2)++fin))
  refine ⟨14+2*(8+3*k)+1,by omega,?_⟩
  simpa only [scanRoot,root,ite_false,Bool.false_eq_true,enc,enc_zero_end,List.append_assoc] using z

theorem scan (second : Bool) (k : Nat) (bs : List Bool) : ∃ t, 0<t ∧
    run0 p t (scanRoot second k bs) = some (root (next second (k+1) bs).1 (next second (k+1) bs).2) := by
  induction bs generalizing k with
  | nil => cases second
           · exact endPrimary k
           · exact endSecondary k
  | cons b bs ih =>
    cases b
    · cases second
      · exact zeroPrimary k bs
      · exact zeroSecondary k bs
    · obtain ⟨t,ht,hr⟩ := ih (k+1)
      exact ⟨26+t,by omega,join0 (carryOne second k bs) hr⟩

-- The empty primary digit word is a transient special case, so the seed uses one digit.
def advance (second : Bool) (bs : List Bool) : Bool × List Bool :=
  if bs.isEmpty then (false,[false]) else next second 0 bs

theorem growth (second : Bool) (bs : List Bool) : ∃ t, 0<t ∧
    run0 p t (root second bs) = some (root (advance second bs).1 (advance second bs).2) := by
  cases bs with
  | nil => cases second
           · exact ⟨100,by decide,firstEnd0⟩
           · exact ⟨50,by decide,firstEnd1⟩
  | cons b bs =>
    cases b
    · cases second
      · exact ⟨44,by decide,firstZero0 (enc bs)⟩
      · exact ⟨44,by decide,firstZero1 (enc bs)⟩
    · obtain ⟨t,ht,hr⟩ := scan second 0 bs
      cases second
      · exact ⟨54+t,by omega,join0 (firstCarry0 bs) hr⟩
      · exact ⟨51+t,by omega,join0 (firstCarry1 bs) hr⟩

def trajectory : Nat → Bool × List Bool
  | 0 => (false,[])
  | n+1 => advance (trajectory n).1 (trajectory n).2

def family (n : Nat) : Z0 := root (trajectory n).1 (trajectory n).2
theorem init : run0 p 561 (A [] []) = some (family 0) := rfl

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  let cost := fun n => Classical.choose (growth (trajectory n).1 (trajectory n).2)
  exact never_of_growth p family 561 cost init
    (fun n => (Classical.choose_spec (growth (trajectory n).1 (trajectory n).2)).1)
    (fun n => (Classical.choose_spec (growth (trajectory n).1 (trajectory n).2)).2) m hm

#print axioms never
#print axioms growth
#print axioms init
end BB6.Agent46Raw13Coupled6RFOneRD
