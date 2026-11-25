import BlockPump

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BB6.Agent2Raw124ZeroLFHard1
open BB6Coverage BB6Coverage.Agent50Pump BB6Coverage.Agent50Zipper

def p1 : PartialMachine := fun s =>
  ([some (some ⟨true,true,1⟩), none,
    some (some ⟨true,true,2⟩), some (some ⟨true,true,5⟩),
    some (some ⟨false,true,3⟩), some (some ⟨false,true,1⟩),
    some (some ⟨true,false,3⟩), some (some ⟨true,true,4⟩),
    some (some ⟨false,true,0⟩), some (some ⟨true,false,5⟩),
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
private theorem scan (n : Nat) (l x : List Bool) :
    hrun p1 (4*n) (front l (rep a n ++ x)) = some (front (rep b n ++ l) x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have h : hrun p1 4 (front (rep b n ++ l) (a++x)) =
        some (front (b++rep b n++l) x) := by
      simpa only [List.append_assoc] using (show hrun p1 4 (front (rep b n ++ l) (a++x)) = some (front (b++(rep b n++l)) x) by rfl)
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
    hrun p1 25 (sec n x) = some (front (ones 4) (rep a n ++ x)) := by rfl

private theorem leaveScan (l x : List Bool) :
    hrun p1 4 (front l x) = some (f (b++l) (false::x)) := by
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
    hrun p1 n ⟨5,ones n ++ l,r⟩ = some ⟨5,l,zeros n ++ r⟩ := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    have h : hrun p1 1 ⟨5,ones (n+1) ++ l,r⟩ = some ⟨5,ones n ++ l,false::r⟩ := by rfl
    have hh := hjoin h (ih (false::r))
    rw [show 1+n=n+1 by omega] at hh
    rw [show zeros (n+1) ++ r = zeros n ++ false::r by simp [zeros,List.replicate_succ',List.append_assoc]]
    exact hh

private theorem backInit (l x : List Bool) :
    hrun p1 7 (back l x) = some ⟨5,true::true::l,true::true::x⟩ := by rfl

private theorem backStep (k : Nat) (l x : List Bool) :
    hrun p1 (k+10) (back (ones (k+1) ++ false::l) x) =
      some (back l (zeros k ++ true::true::x)) := by
  have h := hjoin (backInit (ones (k+1) ++ false::l) x)
    (sweepOnes (k+3) (false::l) (true::true::x))
  rw [show 7+(k+3)=k+10 by omega] at h
  have hl : true::true::(ones (k+1) ++ false::l) = ones (k+3) ++ false::l := by rfl
  have hr : zeros (k+3) ++ true::true::x = [false,false,false]++(zeros k++true::true::x) := by rfl
  rw [hr] at h
  exact h

private theorem backAll (n : Nat) (x : List Bool) :
    hrun p1 (12*n+15) (back (bst n) x) = some (sec n (true::true::x)) := by
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
    hrun p1 (25+4*n+4) (sec n x) = some (f (b++stk n) (false::x)) := by
  exact hjoin (hjoin (enter n x) (scan n (ones 4) x)) (leaveScan (stk n) x)

private theorem zeroEntry (l x : List Bool) :
    hrun p1 10 (f (b++l) (false::false::false::x)) =
      some (back (true::true::l) (true::true::x)) := by rfl

private theorem zeroReturn (n : Nat) (x : List Bool) :
    ∃ k, 0 < k ∧ hrun p1 k (sec n (false::false::x)) = some (sec n (ones 4++x)) := by
  have h := hjoin (scanPrefix n (false::false::x)) (zeroEntry (stk n) x)
  have he : true::true::stk n = bst n := leftRotate n
  rw [he] at h
  have hh := hjoin h (backAll n (true::true::x))
  exact ⟨_,by omega,hh⟩

private theorem oneEntry (l z : List Bool) :
    hrun p1 6 (f (b++l) (false::(ones 4++z))) =
      some (f (c++true::true::l) (false::false::true::z)) := by rfl

private theorem oneStart (n : Nat) (z : List Bool) :
    hrun p1 (25+4*n+4+6) (sec n (ones 4++z)) =
      some (f (c++bst n) (false::false::true::z)) := by
  have h := hjoin (scanPrefix n (ones 4++z)) (oneEntry (stk n) z)
  rw [show c++true::true::stk n = c++bst n by exact congrArg (c++·) (leftRotate n)] at h
  exact h


private theorem prefAdvance (n : Nat) (x : List Bool) :
    sec n (a++x) = sec (n+1) x := by
  have commute : rep a n ++ a = a ++ rep a n := by
    induction n with
    | zero => simp [rep]
    | succ n ih => simp only [rep,List.append_assoc,ih]
  simp only [sec,rep,List.append_assoc,← commute]

private abbrev Digit := Bool × Bool
private def digit (d : Digit) (h : Bool) : List Bool :=
  [d.1,d.1,d.2,d.2,d.2,d.2,h,h,d.1||d.2,d.1||d.2,d.1||d.2,d.1||d.2]
private def low (ds : List Digit) : Bool := (ds.headD (false,false)).1
private def enc : List Digit → List Bool
  | [] => []
  | d::ds => digit d (low ds) ++ enc ds
private def phase (n : Nat) (ds : List Digit) : HZ := sec n (ones 4 ++ enc ds)
private def inc : List Digit → List Digit
  | [] => [(true,false)]
  | (false,b)::ds => (true,b)::ds
  | (true,false)::ds => (false,true)::ds
  | (true,true)::ds => (false,false)::inc ds

private theorem zeroRun (k : Nat) (ds : List Digit) (h : low ds = false) :
    enc (List.replicate k (false,false)++ds) = zeros (12*k)++enc ds := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 12*(k+1)=12*k+12 by omega]
    cases k with
    | zero => change digit (false,false) (low ds) ++ enc ds = _; rw [h]; rfl
    | succ k =>
      change digit (false,false) false ++ enc (List.replicate (k+1) (false,false)++ds) = _
      rw [ih]
      rfl

private theorem zeroRunLast (k : Nat) (ds : List Digit) (h : low ds = true) :
    enc (List.replicate (k+1) (false,false)++ds) =
      zeros (12*k)++digit (false,false) true++enc ds := by
  induction k with
  | zero => change digit (false,false) (low ds) ++ enc ds = _; rw [h]; rfl
  | succ k ih =>
    rw [show 12*(k+1)=12*k+12 by omega]
    change digit (false,false) false ++ enc (List.replicate (k+1) (false,false)++ds) = _
    rw [ih]
    simp only [List.append_assoc]
    rfl

private def scanCarry (m : Nat) (l x : List Bool) : HZ := f (ones (m+3)++false::l) ([false,false,true]++x)

-- Terminal digit handlers are independent of the length of the left run.
private theorem term0 (m : Nat) (l x : List Bool) (h : Bool) :
    hrun p1 60 (scanCarry m l (digit (false,false) h++x)) =
      some (back (ones (m+5)++false::l) ((if h then zeros 4++ones 6 else zeros 6++ones 4)++x)) := by
  cases h <;> rfl
private theorem term1 (m : Nat) (l x : List Bool) (h : Bool) :
    hrun p1 20 (scanCarry m l (digit (true,false) h++x)) =
      some (back (ones (m+7)++false::l) (true::true::(if h then ones 6 else zeros 2++ones 4)++x)) := by
  cases h <;> rfl
private theorem term2 (m : Nat) (l x : List Bool) (h : Bool) :
    hrun p1 20 (scanCarry m l (digit (false,true) h++x)) =
      some (back (ones (m+5)++false::l) (ones 4++(if h then ones 6 else zeros 2++ones 4)++x)) := by
  cases h <;> rfl
private theorem termEmpty (m : Nat) (l : List Bool) :
    hrun p1 60 (scanCarry m l []) =
      some (back (ones (m+5)++false::l) (zeros 6++ones 4)) := by rfl

private theorem term0Return (m : Nat) (l x : List Bool) (h : Bool) :
    hrun p1 (60+(m+4+10)) (scanCarry m l (digit (false,false) h++x)) =
      some (back l (zeros (m+4)++digit (true,false) h++x)) := by
  cases h with
  | false => simpa only [List.append_assoc,List.cons_append,digit,ones,zeros,List.replicate_succ,List.replicate_zero,List.nil_append,Bool.or_false,Bool.or_true] using hjoin (term0 m l x false) (backStep (m+4) l ((zeros 6++ones 4)++x))
  | true => simpa only [List.append_assoc,List.cons_append,digit,ones,zeros,List.replicate_succ,List.replicate_zero,List.nil_append,Bool.or_false,Bool.or_true] using hjoin (term0 m l x true) (backStep (m+4) l ((zeros 4++ones 6)++x))
private theorem term1Return (m : Nat) (l x : List Bool) (h : Bool) :
    hrun p1 (20+(m+6+10)) (scanCarry m l (digit (true,false) h++x)) =
      some (back l (zeros (m+4)++digit (false,true) h++x)) := by
  have hz : zeros (m+6) = zeros (m+4) ++ [false,false] := by
    unfold zeros
    exact (List.replicate_append_replicate (n:=m+4) (m:=2) (a:=false)).symm
  cases h with
  | false =>
    have hh := hjoin (term1 m l x false) (backStep (m+6) l (true::true::(zeros 2++ones 4)++x))
    rw [hz] at hh
    simpa only [List.append_assoc,List.cons_append,digit,ones,zeros,List.replicate_succ,List.replicate_zero,List.nil_append,Bool.or_false,Bool.or_true] using hh
  | true =>
    have hh := hjoin (term1 m l x true) (backStep (m+6) l (true::true::ones 6++x))
    rw [hz] at hh
    simpa only [List.append_assoc,List.cons_append,digit,ones,zeros,List.replicate_succ,List.replicate_zero,List.nil_append,Bool.or_false,Bool.or_true] using hh
private theorem term2Return (m : Nat) (l x : List Bool) (h : Bool) :
    hrun p1 (20+(m+4+10)) (scanCarry m l (digit (false,true) h++x)) =
      some (back l (zeros (m+4)++digit (true,true) h++x)) := by
  cases h with
  | false => simpa only [List.append_assoc,List.cons_append,digit,ones,zeros,List.replicate_succ,List.replicate_zero,List.nil_append,Bool.or_false,Bool.or_true] using hjoin (term2 m l x false) (backStep (m+4) l (ones 4++(zeros 2++ones 4)++x))
  | true => simpa only [List.append_assoc,List.cons_append,digit,ones,zeros,List.replicate_succ,List.replicate_zero,List.nil_append,Bool.or_false,Bool.or_true] using hjoin (term2 m l x true) (backStep (m+4) l (ones 4++ones 6++x))
private theorem termEmptyReturn (m : Nat) (l : List Bool) :
    hrun p1 (60+(m+4+10)) (scanCarry m l []) =
      some (back l (zeros (m+4)++digit (true,false) false)) := by
  exact hjoin (termEmpty m l) (backStep (m+4) l _)

private theorem fullDigit (k : Nat) (l x : List Bool) :
    hrun p1 36 (scanCarry (12*k) l (digit (true,true) true++x)) =
      some (scanCarry (12*(k+1)) l x) := by
  unfold scanCarry
  rw [show 12*(k+1)+3=(12*k+3)+12 by omega]
  rfl

private theorem splitDigit (k : Nat) (l x : List Bool) :
    hrun p1 28 (scanCarry (12*k) l (digit (true,true) false++x)) =
      some (scanCarry 0 (ones (12*k+11)++false::l) x) := by
  rfl

private theorem lowInc (ds : List Digit) : low (inc ds) = !low ds := by
  cases ds with
  | nil => rfl
  | cons d ds => rcases d with ⟨a,b⟩; cases a <;> cases b <;> rfl

private theorem lowFalseReturn (l : List Bool) (ds : List Digit) (h : low ds = false) :
    ∃ t, 0 < t ∧ hrun p1 t (scanCarry 0 l (enc ds)) = some (back l (zeros 4++enc (inc ds))) := by
  cases ds with
  | nil => exact ⟨_,by decide,termEmptyReturn 0 l⟩
  | cons d ds =>
    rcases d with ⟨a,b⟩
    cases a with
    | true => contradiction
    | false =>
      cases b with
      | false => exact ⟨74,by decide,by simpa only [enc,inc,List.append_assoc] using term0Return 0 l (enc ds) (low ds)⟩
      | true => exact ⟨34,by decide,by simpa only [enc,inc,List.append_assoc] using term2Return 0 l (enc ds) (low ds)⟩

private theorem prependZeros (k : Nat) (x : List Bool) : zeros (12*k+4)++x = zeros 4++zeros (12*k)++x := by rfl

private theorem carryComplete (ds : List Digit) (k : Nat) (l : List Bool) (h : k=0 ∨ low ds=true) :
    ∃ t, 0 < t ∧ hrun p1 t (scanCarry (12*k) l (enc ds)) =
      some (back l (zeros 4++enc (List.replicate k (false,false) ++ inc ds))) := by
  induction ds generalizing k l with
  | nil =>
    have hk : k=0 := by cases h with | inl h => exact h | inr h => contradiction
    subst k
    exact lowFalseReturn l [] rfl
  | cons d ds ih =>
    rcases d with ⟨a,b⟩
    cases a with
    | false =>
      have hk : k=0 := by cases h with | inl h => exact h | inr h => contradiction
      subst k
      exact lowFalseReturn l ((false,b)::ds) rfl
    | true =>
      cases b with
      | false =>
        refine ⟨20+(12*k+6+10),by omega,?_⟩
        rw [zeroRun k (inc ((true,false)::ds)) rfl]
        simpa only [enc,inc,List.append_assoc,prependZeros] using term1Return (12*k) l (enc ds) (low ds)
      | true =>
        have he : List.replicate k (false,false) ++ inc ((true,true)::ds) =
            List.replicate (k+1) (false,false) ++ inc ds := by
          rw [List.replicate_succ',List.append_assoc]
          rfl
        rw [he]
        cases hd : low ds with
        | true =>
          obtain ⟨t,ht,hh⟩ := ih (k+1) l (.inr hd)
          refine ⟨36+t,by omega,?_⟩
          have hj := hjoin (fullDigit k l (enc ds)) hh
          simpa only [enc,hd] using hj
        | false =>
          obtain ⟨t,ht,hh⟩ := lowFalseReturn (ones (12*k+11)++false::l) ds hd
          have hj := hjoin (splitDigit k l (enc ds)) hh
          have hb := hjoin hj (backStep (12*k+10) l (zeros 4++enc (inc ds)))
          refine ⟨28+t+(12*k+10+10),by omega,?_⟩
          rw [zeroRunLast k (inc ds) (by rw [lowInc,hd]; rfl)]
          have hz : zeros (12*k+10) = zeros 4 ++ zeros (12*k) ++ zeros 6 := by
            unfold zeros
            rw [List.replicate_append_replicate,List.replicate_append_replicate]
            congr 1; omega
          rw [hz] at hb
          simpa only [enc,hd,List.append_assoc,List.cons_append,digit,ones,zeros,List.replicate_succ,List.replicate_zero,List.nil_append,Bool.or_false] using hb

private theorem phaseReturn (n : Nat) (ds : List Digit) :
    ∃ t, 0<t ∧ hrun p1 t (phase n ds) = some (phase (n+1) (inc ds)) := by
  obtain ⟨t,ht,hc⟩ := carryComplete ds 0 (bst n) (.inl rfl)
  have hh := hjoin (oneStart n (enc ds)) hc
  have hb := hjoin hh (backAll n (zeros 4++enc (inc ds)))
  have he : sec n (true::true::(zeros 4++enc (inc ds))) = sec (n+1) (false::false::enc (inc ds)) := prefAdvance n _
  rw [he] at hb
  obtain ⟨u,hu,hz⟩ := zeroReturn (n+1) (enc (inc ds))
  exact ⟨_,by omega,hjoin hb hz⟩

private theorem root : hrun p1 54 ⟨0,[],[]⟩ = some (phase 0 []) := by rfl

private theorem arbitraryLive (n : Nat) : ∃ t, n ≤ t ∧ ∃ k ds, hrun p1 t ⟨0,[],[]⟩ = some (phase k ds) := by
  induction n with
  | zero => exact ⟨54,by decide,0,[],root⟩
  | succ n ih =>
    obtain ⟨t,ht,k,ds,hr⟩ := ih
    obtain ⟨u,hu,hp⟩ := phaseReturn k ds
    exact ⟨t+u,by omega,k+1,inc ds,hjoin hr hp⟩
private theorem blank_eq : embed (HZ.at ⟨0,[],[]⟩ 0) = blank := by
  unfold embed HZ.at blank
  congr 1
  funext x
  simp [atCell]

/-- The second hard leaf never queries A1, irrespective of its completion. -/
theorem neverHard1 (m : Machine) (hm : compatible p1 m) : NeverHalts m := by
  intro n
  obtain ⟨k,hk,j,ds,Hk⟩ := arbitraryLive n
  obtain ⟨h',H'⟩ := hrun_sound p1 k _ _ 0 Hk
  have H := zrun_sound p1 m hm k _ _ H'
  rw [blank_eq] at H
  rw [show k=n+(k-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some z => rfl

theorem coverHard1 (bound : Nat) : Cover (DecidedBelow bound) p1 :=
  .leaf _ (fun m hm => Or.inl (neverHard1 m hm))

#print axioms phaseReturn
#print axioms neverHard1
#print axioms coverHard1
end BB6.Agent2Raw124ZeroLFHard1
