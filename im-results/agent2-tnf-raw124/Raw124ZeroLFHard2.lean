import BlockPump

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BB6.Agent2Raw124ZeroLFHard2
open BB6Coverage BB6Coverage.Agent50Pump BB6Coverage.Agent50Zipper

def p2 : PartialMachine := fun s =>
  ([some (some ⟨true,true,1⟩), none,
    some (some ⟨true,true,2⟩), some (some ⟨true,true,5⟩),
    some (some ⟨false,true,3⟩), some (some ⟨false,true,1⟩),
    some (some ⟨true,false,3⟩), some (some ⟨true,true,4⟩),
    some (some ⟨true,true,0⟩), some (some ⟨true,false,5⟩),
    some (some ⟨true,true,1⟩), some (some ⟨false,false,5⟩)] :
    List (Option Transition))[2*s.1.val+s.2.toNat]?.getD none

-- nearest-first words; the scanned cell is the first entry of l
private def rep (w : List Bool) : Nat → List Bool
  | 0 => []
  | n+1 => w ++ rep w n
private def a : List Bool := [true,true,false,false]
private def b : List Bool := [true,false,true,true]
private def c : List Bool := [true,true,true,false]
private def d : List Bool := [false,false,true,true]
private def ones (n : Nat) : List Bool := List.replicate n true
private def zeros (n : Nat) : List Bool := List.replicate n false
private def stk (n : Nat) : List Bool := rep b n ++ ones 4
private def bst (n : Nat) : List Bool := rep c n ++ ones 6
private def sec (n : Nat) (x : List Bool) : HZ := ⟨5,[],zeros 8 ++ rep a n ++ x⟩
private def f (l r : List Bool) : HZ := ⟨5,false::l,r⟩
private def front (l x : List Bool) : HZ := f l ([false,true,true,false,false]++x)
private def back (l x : List Bool) : HZ := f l ([false,false,false]++x)
private def quad : List Bool → List Bool
  | [] => []
  | x::xs => x::x::x::x::quad xs
private def code (v : Bool) (xs : List Bool) : List Bool := v::v::quad xs
private def phase (n : Nat) (z v : Bool) (xs : List Bool) : HZ :=
  sec n (ones 4 ++ [z,z,!z,!z] ++ code v xs)

private theorem scan (n : Nat) (l x : List Bool) :
    hrun p2 (4*n) (front l (rep a n ++ x)) = some (front (rep b n ++ l) x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have h : hrun p2 4 (front (rep b n ++ l) (a++x)) =
        some (front (b++rep b n++l) x) := by
      simpa only [List.append_assoc] using (show hrun p2 4 (front (rep b n ++ l) (a++x)) = some (front (b++(rep b n++l)) x) by rfl)
    have hh := hjoin (ih (a++x)) h
    -- repeated words commute with one additional copy
    have commute : ∀ (w : List Bool) (k : Nat), rep w k ++ w = w ++ rep w k := by
      intro w k
      induction k with
      | zero => simp [rep]
      | succ k ih => simp only [rep,List.append_assoc,ih]
    rw [show 4*n+4=4*(n+1) by omega] at hh
    simpa only [rep,List.append_assoc,← commute a n] using hh

private theorem enter (n : Nat) (x : List Bool) :
    hrun p2 25 (sec n x) = some (front (ones 4) (rep a n ++ x)) := by rfl

private theorem leaveScan (l x : List Bool) :
    hrun p2 4 (front l x) = some (f (b++l) (false::x)) := by
  cases x with
  | nil => rfl
  | cons z zs => rfl

private theorem leftRotate (n : Nat) : [true,true] ++ stk n = bst n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change [true,true] ++ (b ++ rep b n ++ ones 4) = c ++ rep c n ++ ones 6
    have h : [true,true] ++ b = c ++ [true,true] := rfl
    change [true,true] ++ (b ++ stk n) = c ++ bst n
    rw [← List.append_assoc,h,List.append_assoc,ih]

private theorem rightRotate (n : Nat) : [true,true] ++ rep d n = rep a n ++ [true,true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change [true,true] ++ (d ++ rep d n) = a ++ rep a n ++ [true,true]
    have h : [true,true] ++ d = a ++ [true,true] := rfl
    rw [← List.append_assoc,h,List.append_assoc,ih,List.append_assoc]

private theorem sweepOnes (n : Nat) (l r : List Bool) :
    hrun p2 n ⟨5,ones n ++ l,r⟩ = some ⟨5,l,zeros n ++ r⟩ := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    have h : hrun p2 1 ⟨5,ones (n+1) ++ l,r⟩ = some ⟨5,ones n ++ l,false::r⟩ := by rfl
    have hh := hjoin h (ih (false::r))
    rw [show 1+n=n+1 by omega] at hh
    rw [show zeros (n+1) ++ r = zeros n ++ false::r by simp [zeros,List.replicate_succ',List.append_assoc]]
    exact hh

private theorem backInit (l x : List Bool) :
    hrun p2 7 (back l x) = some ⟨5,true::true::l,true::true::x⟩ := by rfl

private theorem backStep (k : Nat) (l x : List Bool) :
    hrun p2 (k+10) (back (ones (k+1) ++ false::l) x) =
      some (back l (zeros k ++ true::true::x)) := by
  have h := hjoin (backInit (ones (k+1) ++ false::l) x)
    (sweepOnes (k+3) (false::l) (true::true::x))
  rw [show 7+(k+3)=k+10 by omega] at h
  have hl : true::true::(ones (k+1) ++ false::l) = ones (k+3) ++ false::l := by rfl
  have hr : zeros (k+3) ++ true::true::x = [false,false,false]++(zeros k++true::true::x) := by rfl
  rw [hr] at h
  exact h

private theorem backAll (n : Nat) (x : List Bool) :
    hrun p2 (12*n+15) (back (bst n) x) = some (sec n (true::true::x)) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have h := backStep 2 (bst n) x
    have hh := hjoin h (ih (d++x))
    have he : sec n (true::true::(d++x)) = sec (n+1) (true::true::x) := by
      unfold sec
      congr 1
      have commute : ∀ k, rep a k ++ a = a ++ rep a k := by
        intro k
        induction k with
        | zero => simp [rep]
        | succ k ih => rw [rep, List.append_assoc, ih, ← List.append_assoc]
      change zeros 8 ++ (rep a n ++ (a ++ true::true::x)) = zeros 8 ++ ((a ++ rep a n) ++ true::true::x)
      rw [← List.append_assoc (rep a n),commute]
    rw [he,show 2+10+(12*n+15)=12*(n+1)+15 by omega] at hh
    have hs : ones (2+1) ++ false::bst n = bst (n+1) := by rfl
    rw [hs] at hh
    exact hh

private theorem scanPrefix (n : Nat) (x : List Bool) :
    hrun p2 (25+4*n+4) (sec n x) = some (f (b++stk n) (false::x)) := by
  exact hjoin (hjoin (enter n x) (scan n (ones 4) x)) (leaveScan (stk n) x)

private theorem zeroEntry (l x : List Bool) :
    hrun p2 10 (f (b++l) (false::false::false::x)) =
      some (back (true::true::l) (true::true::x)) := by rfl

private theorem zeroReturn (n : Nat) (x : List Bool) :
    ∃ k, 0 < k ∧ hrun p2 k (sec n (false::false::x)) = some (sec n (ones 4++x)) := by
  have h := hjoin (scanPrefix n (false::false::x)) (zeroEntry (stk n) x)
  have he : true::true::stk n = bst n := leftRotate n
  rw [he] at h
  have hh := hjoin h (backAll n (true::true::x))
  exact ⟨_,by omega,hh⟩

private theorem oneEntry (l z : List Bool) :
    hrun p2 6 (f (b++l) (false::(ones 4++z))) =
      some (f (c++true::true::l) (false::false::true::z)) := by rfl

private theorem oneStart (n : Nat) (z : List Bool) :
    hrun p2 (25+4*n+4+6) (sec n (ones 4++z)) =
      some (f (c++bst n) (false::false::true::z)) := by
  have h := hjoin (scanPrefix n (ones 4++z)) (oneEntry (stk n) z)
  rw [show c++true::true::stk n = c++bst n by exact congrArg (c++·) (leftRotate n)] at h
  exact h

private theorem phase0Step (l w : List Bool) :
    hrun p2 12 (f (c++l) ([false,false,true,false,false,true,true]++w)) =
      some (back (ones 5++false::l) (false::false::w)) := by rfl

private theorem prefAdvance (n : Nat) (x : List Bool) :
    sec n (a++x) = sec (n+1) x := by
  have commute : rep a n ++ a = a ++ rep a n := by
    induction n with
    | zero => simp [rep]
    | succ n ih => simp only [rep,List.append_assoc,ih]
  simp only [sec,rep,List.append_assoc,← commute]

private theorem phase0Return (n : Nat) (v : Bool) (xs : List Bool) :
    ∃ k, 0 < k ∧ hrun p2 k (phase n false v xs) = some (phase (n+1) true v xs) := by
  have h := hjoin (oneStart n ([false,false,true,true]++code v xs))
    (phase0Step (bst n) (code v xs))
  have h' := hjoin h (backStep 4 (bst n) (false::false::code v xs))
  have h'' := hjoin h' (backAll n (zeros 4++true::true::false::false::code v xs))
  have he : sec n (true::true::(zeros 4++true::true::false::false::code v xs)) =
      sec (n+1) (false::false::true::true::false::false::code v xs) := by
    exact prefAdvance n _
  rw [he] at h''
  obtain ⟨t,ht,hz⟩ := zeroReturn (n+1) (true::true::false::false::code v xs)
  exact ⟨_,by omega,hjoin h'' hz⟩

private theorem phase1Advance (l w : List Bool) :
    hrun p2 6 (f (c++l) ([false,false,true,true,true,false,false]++w)) =
      some (front (ones 5++false::l) w) := by rfl

private theorem phase1Start (n : Nat) (v : Bool) (xs : List Bool) :
    hrun p2 (25+4*n+4+6+6+4) (phase n true v xs) =
      some (f (b++ones 5++false::bst n) (false::code v xs)) := by
  exact hjoin (hjoin (oneStart n ([true,true,false,false]++code v xs))
    (phase1Advance (bst n) (code v xs))) (leaveScan (ones 5++false::bst n) (code v xs))

private theorem firstZeroReturn (n : Nat) (xs : List Bool) :
    ∃ k, 0 < k ∧ hrun p2 k (phase n true false xs) = some (phase (n+1) false true xs) := by
  have h := hjoin (phase1Start n false xs) (zeroEntry (ones 5++false::bst n) (quad xs))
  have h' := hjoin h (backStep 6 (bst n) (true::true::quad xs))
  have h'' := hjoin h' (backAll n (zeros 6++true::true::true::true::quad xs))
  have he : sec n (true::true::(zeros 6++true::true::true::true::quad xs)) =
      sec (n+1) (false::false::[false,false,true,true]++code true xs) := by
    exact prefAdvance n _
  rw [he] at h''
  obtain ⟨t,ht,hz⟩ := zeroReturn (n+1) ([false,false,true,true]++code true xs)
  exact ⟨_,by omega,hjoin h'' hz⟩

private def carryStart (l : List Bool) (xs : List Bool) : HZ :=
  f (b++ones 5++false::l) ([false,true,true]++quad xs)
private def carryLoop (k : Nat) (l : List Bool) (xs : List Bool) : HZ :=
  f (ones (4*k+5)++false::ones 7++false::l) ([false,true,true]++quad xs)

private theorem startStop (l : List Bool) (xs : List Bool) :
    hrun p2 14 (carryStart l (false::xs)) =
      some (back (ones 3++false::ones 7++false::l) (true::true::quad xs)) := by rfl
private theorem startEmpty (l : List Bool) :
    hrun p2 14 (carryStart l []) =
      some (back (ones 3++false::ones 7++false::l) [true,true]) := by rfl
private theorem startOne (l : List Bool) (xs : List Bool) :
    hrun p2 12 (carryStart l (true::xs)) = some (carryLoop 0 l xs) := by rfl

private theorem loopOne (k : Nat) (l : List Bool) (xs : List Bool) :
    hrun p2 12 (carryLoop k l (true::xs)) = some (carryLoop (k+1) l xs) := by
  unfold carryLoop
  rw [show 4*(k+1)+5=(4*k+5)+4 by omega]
  rfl
private theorem loopStop (k : Nat) (l : List Bool) (xs : List Bool) :
    hrun p2 14 (carryLoop k l (false::xs)) =
      some (back (ones (4*(k+1)+3)++false::ones 7++false::l) (true::true::quad xs)) := by
  unfold carryLoop
  rw [show 4*(k+1)+3=(4*k+5)+2 by omega]
  rfl
private theorem loopEmpty (k : Nat) (l : List Bool) :
    hrun p2 14 (carryLoop k l []) =
      some (back (ones (4*(k+1)+3)++false::ones 7++false::l) [true,true]) := by
  unfold carryLoop
  rw [show 4*(k+1)+3=(4*k+5)+2 by omega]
  rfl

private theorem quadZeros (k : Nat) (xs : List Bool) :
    quad (List.replicate k false ++ xs) = zeros (4*k) ++ quad xs := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 4*(k+1)=4*k+4 by omega]
    change false::false::false::false::quad (List.replicate k false++xs) =
      false::false::false::false::(zeros (4*k)++quad xs)
    rw [ih]

private theorem finishCarry (n k : Nat) (xs : List Bool) :
    ∃ t, 0 < t ∧ hrun p2 t (back (ones (4*k+3)++false::ones 7++false::bst n) (true::true::quad xs)) =
      some (phase (n+1) false false (List.replicate k false ++ true::xs)) := by
  have h := hjoin (backStep (4*k+2) (ones 7++false::bst n) (true::true::quad xs))
    (backStep 6 (bst n) (zeros (4*k+2)++true::true::true::true::quad xs))
  have h' := hjoin h (backAll n (zeros 6++true::true::(zeros (4*k+2)++true::true::true::true::quad xs)))
  have he : sec n (true::true::(zeros 6++true::true::(zeros (4*k+2)++true::true::true::true::quad xs))) =
      sec (n+1) (false::false::[false,false,true,true]++code false (List.replicate k false ++ true::xs)) := by
    unfold code
    rw [quadZeros]
    exact prefAdvance n _
  rw [he] at h'
  obtain ⟨t,ht,hz⟩ := zeroReturn (n+1) ([false,false,true,true]++code false (List.replicate k false ++ true::xs))
  refine ⟨(4*k+2+10)+(6+10)+(12*n+15)+t,by omega,?_⟩
  simpa only [List.append_assoc,List.cons_append,phase,Bool.not_false] using hjoin h' hz

private theorem loopReturn (n k : Nat) (xs : List Bool) :
    ∃ t ys, 0 < t ∧ hrun p2 t (carryLoop k (bst n) xs) = some (phase (n+1) false false ys) := by
  induction xs generalizing k with
  | nil =>
    obtain ⟨t,ht,h⟩ := finishCarry n (k+1) []
    exact ⟨14+t,_,by omega,hjoin (loopEmpty k (bst n)) h⟩
  | cons b xs ih =>
    cases b with
    | false =>
      obtain ⟨t,ht,h⟩ := finishCarry n (k+1) xs
      exact ⟨14+t,_,by omega,hjoin (loopStop k (bst n) xs) h⟩
    | true =>
      obtain ⟨t,ys,ht,h⟩ := ih (k+1)
      exact ⟨12+t,ys,by omega,hjoin (loopOne k (bst n) xs) h⟩

private theorem firstOneReturn (n : Nat) (xs : List Bool) :
    ∃ t ys, 0 < t ∧ hrun p2 t (phase n true true xs) = some (phase (n+1) false false ys) := by
  have h := phase1Start n true xs
  change hrun p2 _ (phase n true true xs) = some (carryStart (bst n) xs) at h
  cases xs with
  | nil =>
    obtain ⟨t,ht,hr⟩ := finishCarry n 0 []
    exact ⟨_,_,by omega,hjoin (hjoin h (startEmpty (bst n))) hr⟩
  | cons b xs =>
    cases b with
    | false =>
      obtain ⟨t,ht,hr⟩ := finishCarry n 0 xs
      exact ⟨_,_,by omega,hjoin (hjoin h (startStop (bst n) xs)) hr⟩
    | true =>
      obtain ⟨t,ys,ht,hr⟩ := loopReturn n 0 xs
      exact ⟨_,ys,by omega,hjoin (hjoin h (startOne (bst n) xs)) hr⟩

/-- Every encoded phase has a strictly later encoded phase, for arbitrary finite bits. -/
private theorem phaseReturn (n : Nat) (z v : Bool) (xs : List Bool) :
    ∃ t z' v' ys, 0 < t ∧ hrun p2 t (phase n z v xs) = some (phase (n+1) z' v' ys) := by
  cases z with
  | false =>
    obtain ⟨t,ht,h⟩ := phase0Return n v xs
    exact ⟨t,true,v,xs,ht,h⟩
  | true =>
    cases v with
    | false =>
      obtain ⟨t,ht,h⟩ := firstZeroReturn n xs
      exact ⟨t,false,true,xs,ht,h⟩
    | true =>
      obtain ⟨t,ys,ht,h⟩ := firstOneReturn n xs
      exact ⟨t,false,false,ys,ht,h⟩

private theorem root : hrun p2 850 ⟨0,[],[]⟩ = some (phase 4 false true []) := by rfl

private theorem arbitrary_live (n : Nat) :
    ∃ k j z v xs, n ≤ k ∧ hrun p2 k ⟨0,[],[]⟩ = some (phase j z v xs) := by
  induction n with
  | zero => exact ⟨850,4,false,true,[],by decide,root⟩
  | succ n ih =>
    obtain ⟨k,j,z,v,xs,hk,h⟩ := ih
    obtain ⟨t,z',v',ys,ht,hr⟩ := phaseReturn j z v xs
    exact ⟨k+t,j+1,z',v',ys,by omega,hjoin h hr⟩

private theorem blank_eq : embed (HZ.at ⟨0,[],[]⟩ 0) = blank := by
  unfold embed HZ.at blank
  congr 1
  funext x
  simp [atCell]

/-- The third hard leaf never queries A1, irrespective of its completion. -/
theorem neverHard2 (m : Machine) (hm : compatible p2 m) : NeverHalts m := by
  intro n
  obtain ⟨k,j,z,v,xs,hk,Hk⟩ := arbitrary_live n
  obtain ⟨h',H'⟩ := hrun_sound p2 k _ _ 0 Hk
  have H := zrun_sound p2 m hm k _ _ H'
  rw [blank_eq] at H
  rw [show k=n+(k-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some z => rfl

theorem coverHard2 (bound : Nat) : Cover (DecidedBelow bound) p2 :=
  .leaf _ (fun m hm => Or.inl (neverHard2 m hm))

#print axioms phaseReturn
#print axioms neverHard2
#print axioms coverHard2
end BB6.Agent2Raw124ZeroLFHard2
