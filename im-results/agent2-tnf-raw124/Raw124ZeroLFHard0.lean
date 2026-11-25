import BlockPump

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BB6.Agent2Raw124ZeroLFHard0
open BB6Coverage BB6Coverage.Agent50Pump BB6Coverage.Agent50Zipper

def p0 : PartialMachine := fun s =>
  ([some (some ⟨true,true,1⟩), some (some ⟨false,false,4⟩),
    some (some ⟨true,true,2⟩), some (some ⟨true,true,0⟩),
    some (some ⟨false,true,3⟩), some (some ⟨false,true,1⟩),
    some (some ⟨true,false,3⟩), some (some ⟨true,true,4⟩),
    none, some (some ⟨true,false,5⟩),
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
private def fa (l r : List Bool) : HZ := ⟨0,false::l,r⟩
private theorem af (k : Nat) (l r : List Bool) : hrun p0 (k+1) (fa l r) = hrun p0 (k+1) (f l r) := by rfl
private def front (l x : List Bool) : HZ := fa l ([false,true,true,false,false]++x)
private def back (l x : List Bool) : HZ := f l ([false,false,false]++x)
private theorem scan (n : Nat) (l x : List Bool) :
    hrun p0 (4*n) (front l (rep a n ++ x)) = some (front (rep b n ++ l) x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have h : hrun p0 4 (front (rep b n ++ l) (a++x)) =
        some (front (b++rep b n++l) x) := by
      simpa only [List.append_assoc] using (show hrun p0 4 (front (rep b n ++ l) (a++x)) = some (front (b++(rep b n++l)) x) by rfl)
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
    hrun p0 25 (sec n x) = some (f (ones 4) ([false,true,true,false,false]++rep a n++x)) := by
  rfl

private theorem leaveScan (l x : List Bool) :
    hrun p0 4 (front l x) = some (fa (b++l) (false::x)) := by
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
    hrun p0 n ⟨5,ones n ++ l,r⟩ = some ⟨5,l,zeros n ++ r⟩ := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    have h : hrun p0 1 ⟨5,ones (n+1) ++ l,r⟩ = some ⟨5,ones n ++ l,false::r⟩ := by rfl
    have hh := hjoin h (ih (false::r))
    rw [show 1+n=n+1 by omega] at hh
    rw [show zeros (n+1) ++ r = zeros n ++ false::r by simp [zeros,List.replicate_succ',List.append_assoc]]
    exact hh

private theorem backInit (l x : List Bool) :
    hrun p0 7 (back l x) = some ⟨5,true::true::l,true::true::x⟩ := by rfl

private theorem backStep (k : Nat) (l x : List Bool) :
    hrun p0 (k+10) (back (ones (k+1) ++ false::l) x) =
      some (back l (zeros k ++ true::true::x)) := by
  have h := hjoin (backInit (ones (k+1) ++ false::l) x)
    (sweepOnes (k+3) (false::l) (true::true::x))
  rw [show 7+(k+3)=k+10 by omega] at h
  have hl : true::true::(ones (k+1) ++ false::l) = ones (k+3) ++ false::l := by rfl
  have hr : zeros (k+3) ++ true::true::x = [false,false,false]++(zeros k++true::true::x) := by rfl
  rw [hr] at h
  exact h

private theorem backAll (n : Nat) (x : List Bool) :
    hrun p0 (12*n+15) (back (bst n) x) = some (sec n (true::true::x)) := by
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
    hrun p0 (25+4*n+4) (sec n x) = some (fa (b++stk n) (false::x)) := by
  have hh := hjoin (scan n (ones 4) x) (leaveScan (stk n) x)
  change hrun p0 (4*n+4) (fa (ones 4) ([false,true,true,false,false]++(rep a n++x))) = _ at hh
  rw [af] at hh
  have he := enter n x
  rw [List.append_assoc] at he
  have h := hjoin he hh
  simpa only [Nat.add_assoc] using h

private theorem zeroEntry (l x : List Bool) :
    hrun p0 10 (fa (b++l) (false::false::false::x)) =
      some (back (true::true::l) (true::true::x)) := by rfl

private theorem zeroReturn (n : Nat) (x : List Bool) :
    ∃ k, 0 < k ∧ hrun p0 k (sec n (false::false::x)) = some (sec n (ones 4++x)) := by
  have h := hjoin (scanPrefix n (false::false::x)) (zeroEntry (stk n) x)
  have he : true::true::stk n = bst n := leftRotate n
  rw [he] at h
  have hh := hjoin h (backAll n (true::true::x))
  exact ⟨_,by omega,hh⟩

private theorem oneEntry (l z : List Bool) :
    hrun p0 6 (fa (b++l) (false::(ones 4++z))) =
      some (f (c++true::true::l) (true::false::true::z)) := by rfl

private theorem oneStart (n : Nat) (z : List Bool) :
    hrun p0 (25+4*n+4+6) (sec n (ones 4++z)) =
      some (f (c++bst n) (true::false::true::z)) := by
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


private def Z : List Bool := [false,false,false,false]
private def O : List Bool := [true,true]
private def X : List Bool := [false,true,false,true]

/-- Two mutually recursive word languages, indexed by parity of the number of pairs. -/
private inductive Word : Bool → List Bool → Prop where
  | nil : Word false []
  | pz {x} : Word false x → Word false (Z++x)
  | po {x} : Word false x → Word false (O++O++x)
  | px {x} : Word false x → Word false (X++x)
  | psz {x} : Word true x → Word false (O++Z++x)
  | psx {x} : Word true x → Word false (O++X++x)
  | ho {x} : Word false x → Word true (O++x)
  | hz {x} : Word true x → Word true (Z++x)
  | hx {x} : Word true x → Word true (X++x)

private inductive Raised : List Bool → Prop where
  | z {x} : Word true x → Raised (Z++x)
  | x {x} : Word true x → Raised (X++x)

private theorem raisedH {x} (h : Raised x) : Word true x := by
  cases h with
  | z h => exact .hz h
  | x h => exact .hx h

private theorem raisedP {x} (h : Raised x) : Word false (O++x) := by
  cases h with
  | z h => simpa only [List.append_assoc] using Word.psz h
  | x h => simpa only [List.append_assoc] using Word.psx h

private theorem hPrependO {x} (h : Word true x) : Word false (O++x) := by
  cases h with
  | ho h => simpa only [List.append_assoc] using Word.po h
  | hz h => simpa only [List.append_assoc] using Word.psz h
  | hx h => simpa only [List.append_assoc] using Word.psx h

private def s (n : Nat) (l x : List Bool) : HZ := fa (ones (2*n+1)++false::l) (true::false::true::x)
private def sf (n : Nat) (l x : List Bool) : HZ := f (ones (2*n+1)++false::l) (true::false::true::x)
private theorem s_af (t n : Nat) (l x : List Bool) (ht : 0<t) :
    hrun p0 t (s n l x) = hrun p0 t (sf n l x) := by
  cases t with
  | zero => omega
  | succ t => rfl

private theorem sO (n : Nat) (l x : List Bool) :
    hrun p0 (6+(2*n+4)) (s n l (O++x)) = some (back l (zeros (2*n)++X++x)) := by
  have h : hrun p0 6 (s n l (O++x)) = some ⟨5,ones (2*n+4)++false::l,true::false::true::x⟩ := by rfl
  have hh := hjoin h (sweepOnes (2*n+4) (false::l) (true::false::true::x))
  have hz : zeros (2*n+4) = [false,false,false]++zeros (2*n)++[false] := by
    unfold zeros
    rw [List.replicate_succ',show List.replicate (2*n+3) false = [false,false,false]++List.replicate (2*n) false by rfl]
  rw [hz] at hh
  simpa only [back,f,List.append_assoc,List.cons_append,X,List.nil_append] using hh

private theorem sZZ (n : Nat) (l x : List Bool) :
    hrun p0 (11+(2*n+7)) (s n l (Z++x)) = some (back l (zeros (2*n)++Z++O++x)) := by
  have h : hrun p0 11 (s n l (Z++x)) = some ⟨5,ones (2*n+7)++false::l,O++x⟩ := by rfl
  have hh := hjoin h (sweepOnes (2*n+7) (false::l) (O++x))
  have hz : zeros (2*n+7) = [false,false,false]++zeros (2*n)++Z := by
    unfold zeros Z
    rw [List.replicate_succ',List.replicate_succ',List.replicate_succ',List.replicate_succ']
    simp only [List.append_assoc]
    rfl
  rw [hz] at hh
  simpa only [back,f,List.append_assoc] using hh

private theorem sEmpty (n : Nat) (l : List Bool) :
    hrun p0 (11+(2*n+7)) (s n l []) = some (back l (zeros (2*n)++Z++O)) := by
  have h : hrun p0 11 (s n l []) = some ⟨5,ones (2*n+7)++false::l,O⟩ := by rfl
  have hh := hjoin h (sweepOnes (2*n+7) (false::l) O)
  have hz : zeros (2*n+7) = [false,false,false]++zeros (2*n)++Z := by
    unfold zeros Z
    rw [List.replicate_succ',List.replicate_succ',List.replicate_succ',List.replicate_succ']
    simp only [List.append_assoc]
    rfl
  rw [hz] at hh
  simpa only [back,f,List.append_assoc] using hh

private theorem sXX (n : Nat) (l x : List Bool) :
    hrun p0 4 (s n l (X++x)) = some (s (n+2) l x) := by
  unfold s
  rw [show 2*(n+2)+1=(2*n+1)+4 by omega]
  rfl

private theorem sZOO (n : Nat) (l x : List Bool) :
    hrun p0 10 (s n l ([false,false]++O++O++x)) = some (sf (n+3) l x) := by
  unfold s sf
  rw [show 2*(n+3)+1=(2*n+1)+6 by omega]
  rfl

private theorem sZOZZ (n : Nat) (l x : List Bool) :
    hrun p0 18 (s n l ([false,false]++O++Z++x)) = some (back (ones (2*n+7)++false::l) (O++x)) := by rfl
private theorem sZOEmpty (n : Nat) (l : List Bool) :
    hrun p0 18 (s n l ([false,false]++O)) = some (back (ones (2*n+7)++false::l) O) := by rfl
private theorem sZOXX (n : Nat) (l x : List Bool) :
    hrun p0 8 (s n l ([false,false]++O++X++x)) = some (s 0 (ones (2*n+7)++false::l) x) := by rfl

private theorem appendZeros (n : Nat) (x : List Bool) :
    zeros (2*(n+2))++x = zeros (2*n)++Z++x := by
  unfold zeros Z
  rw [show 2*(n+2)=2*n+4 by omega]
  rw [← List.replicate_append_replicate (n:=2*n) (m:=4) (a:=false)]
  rfl

private def Out (b : Bool) (x : List Bool) : Prop := if b then Word false x else Raised x

/-- The scan consumes an arbitrary word in either language and returns a word
in the other language (with a constrained prefix in the even case). -/
private theorem sReturn {b : Bool} {x : List Bool} (h : Word b x) (n : Nat) (l : List Bool) :
    ∃ t y, 0<t ∧ Out b y ∧ hrun p0 t (s n l x) = some (back l (zeros (2*n)++y)) := by
  induction h generalizing n l with
  | nil =>
    exact ⟨11+(2*n+7),Z++O,by omega,Raised.z (Word.ho Word.nil),by simpa only [List.append_assoc] using sEmpty n l⟩
  | @pz x h ih =>
    exact ⟨11+(2*n+7),Z++O++x,by omega,by simpa only [Out,ite_false,Bool.false_eq_true,List.append_assoc] using Raised.z (Word.ho h),by simpa only [List.append_assoc] using sZZ n l x⟩
  | @po x h ih =>
    exact ⟨6+(2*n+4),X++O++x,by omega,by simpa only [Out,ite_false,Bool.false_eq_true,List.append_assoc] using Raised.x (Word.ho h),by simpa only [List.append_assoc] using sO n l (O++x)⟩
  | @px x h ih =>
    obtain ⟨t,y,ht,hy,hr⟩ := ih (n+2) l
    have hy' : Raised y := hy
    have hh := hjoin (sXX n l x) hr
    rw [appendZeros] at hh
    exact ⟨4+t,Z++y,by omega,Raised.z (raisedH hy'),by simpa only [List.append_assoc] using hh⟩
  | @psz x h ih =>
    exact ⟨6+(2*n+4),X++Z++x,by omega,by simpa only [Out,ite_false,Bool.false_eq_true,List.append_assoc] using Raised.x (Word.hz h),by simpa only [List.append_assoc] using sO n l (Z++x)⟩
  | @psx x h ih =>
    exact ⟨6+(2*n+4),X++X++x,by omega,by simpa only [Out,ite_false,Bool.false_eq_true,List.append_assoc] using Raised.x (Word.hx h),by simpa only [List.append_assoc] using sO n l (X++x)⟩
  | @ho x h ih =>
    exact ⟨6+(2*n+4),X++x,by omega,Word.px h,by simpa only [List.append_assoc] using sO n l x⟩
  | @hz x h ih =>
    exact ⟨11+(2*n+7),Z++O++x,by omega,by simpa only [Out,ite_true,List.append_assoc] using Word.pz (hPrependO h),by simpa only [List.append_assoc] using sZZ n l x⟩
  | @hx x h ih =>
    obtain ⟨t,y,ht,hy,hr⟩ := ih (n+2) l
    have hy' : Word false y := hy
    have hh := hjoin (sXX n l x) hr
    rw [appendZeros] at hh
    exact ⟨4+t,Z++y,by omega,Word.pz hy',by simpa only [List.append_assoc] using hh⟩

private theorem oddReturn {x : List Bool} (h : Word false x) (n : Nat) (l : List Bool) :
    ∃ t y, 0<t ∧ Word false y ∧ hrun p0 t (s n l ([false,false]++O++x)) =
      some (back l (zeros (2*n+6)++y)) := by
  cases h with
  | nil =>
    have hh := hjoin (sZOEmpty n l) (backStep (2*n+6) l O)
    exact ⟨18+(2*n+6+10),O++O,by omega,.po .nil,by simpa only [O,List.nil_append,List.append_nil,List.cons_append,List.append_assoc] using hh⟩
  | @pz x h =>
    have hh := hjoin (sZOZZ n l x) (backStep (2*n+6) l (O++x))
    exact ⟨18+(2*n+6+10),O++O++x,by omega,.po h,by simpa only [O,List.cons_append,List.nil_append,List.append_assoc] using hh⟩
  | @po x h =>
    have hh := sO (n+3) l x
    rw [s_af _ _ _ _ (by omega)] at hh
    have hj := hjoin (sZOO n l (O++x)) hh
    rw [show 2*(n+3)=2*n+6 by omega] at hj
    exact ⟨10+(6+(2*n+6+4)),X++x,by omega,.px h,by simpa only [List.append_assoc] using hj⟩
  | @px x h =>
    obtain ⟨t,y,ht,hy,hr⟩ := sReturn h 0 (ones (2*n+7)++false::l)
    have hy' : Raised y := hy
    have hh := hjoin (sZOXX n l x) hr
    have hj := hjoin hh (backStep (2*n+6) l y)
    exact ⟨8+t+(2*n+6+10),O++y,by omega,raisedP hy',by simpa only [O,List.cons_append,List.nil_append,List.append_assoc] using hj⟩
  | @psz x h =>
    have hh := sZZ (n+3) l x
    rw [s_af _ _ _ _ (by omega)] at hh
    have hj := hjoin (sZOO n l (Z++x)) hh
    rw [show 2*(n+3)=2*n+6 by omega] at hj
    exact ⟨10+(11+(2*n+6+7)),Z++O++x,by omega,by simpa only [List.append_assoc] using Word.pz (hPrependO h),by simpa only [List.append_assoc] using hj⟩
  | @psx x h =>
    obtain ⟨t,y,ht,hy,hr⟩ := sReturn h (n+5) l
    have hy' : Word false y := hy
    have hh := hjoin (sXX (n+3) l x) (show hrun p0 t (s ((n+3)+2) l x) = _ by exact hr)
    rw [s_af _ _ _ _ (by omega)] at hh
    have hj := hjoin (sZOO n l (X++x)) hh
    rw [show 2*(n+5)=2*(n+3+2) by omega] at hr
    have hz : zeros (2*(n+3+2))++y = zeros (2*n+6)++Z++y := by
      simpa only [show 2*(n+3)=2*n+6 by omega] using appendZeros (n+3) y
    rw [hz] at hj
    exact ⟨10+(4+t),Z++y,by omega,.pz hy',by simpa only [List.append_assoc] using hj⟩

private def payload (b : Bool) (x : List Bool) : List Bool := false::false::b::b::x
private def phase (n : Nat) (b : Bool) (x : List Bool) : HZ := sec n (ones 4++payload b x)

private theorem phaseReturn (n : Nat) (b : Bool) {x : List Bool} (hx : Word false x) :
    ∃ t y, 0<t ∧ Word false y ∧ hrun p0 t (phase n b x) = some (phase (n+1) (!b) y) := by
  have h := oneStart n (payload b x)
  change hrun p0 _ (phase n b x) = some (sf 1 (bst n) (payload b x)) at h
  cases b with
  | false =>
    have hh := sZZ 1 (bst n) x
    rw [s_af _ _ _ _ (by omega)] at hh
    have hj := hjoin h hh
    have hb := hjoin hj (backAll n (zeros 2++Z++O++x))
    have he : sec n (true::true::(zeros 2++Z++O++x)) = sec (n+1) (false::false::payload true x) := prefAdvance n _
    rw [he] at hb
    obtain ⟨t,ht,hz⟩ := zeroReturn (n+1) (payload true x)
    exact ⟨_,x,by omega,hx,hjoin hb hz⟩
  | true =>
    obtain ⟨t,y,ht,hy,hr⟩ := oddReturn hx 1 (bst n)
    rw [s_af _ _ _ _ ht] at hr
    have hj := hjoin h hr
    have hb := hjoin hj (backAll n (zeros 8++y))
    have he : sec n (true::true::(zeros 8++y)) = sec (n+1) (false::false::payload false y) := prefAdvance n _
    rw [he] at hb
    obtain ⟨u,hu,hz⟩ := zeroReturn (n+1) (payload false y)
    exact ⟨_,y,by omega,hy,hjoin hb hz⟩

private theorem root : hrun p0 194 ⟨0,[],[]⟩ = some (phase 1 true []) := by rfl

private theorem arbitraryLive (n : Nat) : ∃ t, n≤t ∧ ∃ j b x, Word false x ∧ hrun p0 t ⟨0,[],[]⟩ = some (phase j b x) := by
  induction n with
  | zero => exact ⟨194,by decide,1,true,[],.nil,root⟩
  | succ n ih =>
    obtain ⟨t,ht,j,b,x,hx,hr⟩ := ih
    obtain ⟨u,y,hu,hy,hp⟩ := phaseReturn j b hx
    exact ⟨t+u,by omega,j+1,!b,y,hy,hjoin hr hp⟩
private theorem blank_eq : embed (HZ.at ⟨0,[],[]⟩ 0) = blank := by
  unfold embed HZ.at blank
  congr 1
  funext x
  simp [atCell]

/-- The first hard leaf never queries E0, irrespective of its completion. -/
theorem neverHard0 (m : Machine) (hm : compatible p0 m) : NeverHalts m := by
  intro n
  obtain ⟨k,hk,j,b,x,hx,Hk⟩ := arbitraryLive n
  obtain ⟨h',H'⟩ := hrun_sound p0 k _ _ 0 Hk
  have H := zrun_sound p0 m hm k _ _ H'
  rw [blank_eq] at H
  rw [show k=n+(k-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some z => rfl

theorem coverHard0 (bound : Nat) : Cover (DecidedBelow bound) p0 :=
  .leaf _ (fun m hm => Or.inl (neverHard0 m hm))

#print axioms phaseReturn
#print axioms neverHard0
#print axioms coverHard0
end BB6.Agent2Raw124ZeroLFHard0
