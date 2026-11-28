import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent25M81
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

abbrev P : List Bool := [false,true]
abbrev Q : List Bool := [false,false,true]
abbrev D : List Bool := [true,false]
def ps : Nat → List Bool
  | 0 => []
  | n+1 => P ++ ps n
def ds : Nat → List Bool
  | 0 => []
  | n+1 => D ++ ds n

def A (l r : List Bool) : Z0 := ⟨0,l,r⟩
def B (l r : List Bool) : Z0 := ⟨1,r.headD false::l,r.tail⟩

theorem bP (l r : List Bool) : run0 table 2 (B l (P++r)) = some (B (P++l) r) := rfl
theorem bQ (l r : List Bool) : run0 table 3 (B l (Q++r)) = some (B (Q++l) r) := rfl
theorem bEnd (l : List Bool) : run0 table 8 (B l []) = some (A (true::l) P) := rfl
theorem a0 (l r : List Bool) : run0 table 1 (A (false::l) r) = some (B (true::l) r) := rfl
theorem aBlank (r : List Bool) : run0 table 1 (A [] r) = some (B [true] r) := rfl
theorem a10 (l r : List Bool) : run0 table 2 (A (D++l) r) = some (A l (P++r)) := rfl
theorem a110 (l r : List Bool) : run0 table 5 (A (true::true::false::l) r) = some (B (Q++l) r) := rfl
theorem a1110 (l r : List Bool) : run0 table 5 (A (true::true::true::false::l) r) = some (A (true::l) (Q++r)) := rfl
theorem a1 (r : List Bool) : run0 table 2 (A [true] r) = some (A [] (P++r)) := rfl
theorem a11 (r : List Bool) : run0 table 5 (A [true,true] r) = some (B Q r) := rfl
theorem a111 (r : List Bool) : run0 table 5 (A [true,true,true] r) = some (A [true] (Q++r)) := rfl

theorem ps_snoc (n : Nat) : ps n ++ P = ps (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ps, List.append_assoc, ih]

theorem ds_snoc (n : Nat) : ds n ++ D = ds (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ds, List.append_assoc, ih]

theorem shift (n : Nat) (l : List Bool) : true::(ps n ++ l) = ds n ++ true::l := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ps,ds,List.cons_append,List.nil_append]; exact congrArg (fun x => true::false::x) ih

theorem bSweep (n : Nat) (l r : List Bool) : run0 table (2*n) (B l (ps n++r)) = some (B (ps n++l) r) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    have H := join0 (bP l (ps n++r)) (ih (P++l))
    rw [←List.append_assoc (ps n) P l,ps_snoc] at H
    simpa only [ps,List.append_assoc, show 2+2*n=2*(n+1) by omega] using H

theorem aSweep (n : Nat) (l r : List Bool) : run0 table (2*n) (A (ds n++l) r) = some (A l (ps n++r)) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    have H := join0 (a10 (ds n++l) r) (ih (P++r))
    rw [←List.append_assoc (ps n) P r,ps_snoc] at H
    simpa only [ds,List.append_assoc, show 2+2*n=2*(n+1) by omega] using H

theorem bSweepEnd (n : Nat) (l : List Bool) : run0 table (2*n+8) (B l (ps n)) = some (A (true::(ps n++l)) P) := by
  have H := join0 (bSweep n l []) (bEnd (ps n++l))
  simpa using H

theorem aSweepOne (n : Nat) (l : List Bool) : run0 table (2*n) (A (true::(ps n++l)) P) = some (A (true::l) (ps (n+1))) := by
  rw [shift]
  simpa only [ps_snoc] using aSweep n (true::l) P


/-- Sweep over one double-zero separator, then return left to that separator. -/
theorem bGapReturn (k m : Nat) (l : List Bool) :
    run0 table (2*k+3+(2*m+8)+2*m+2) (B l (ps k++Q++ps m)) =
      some (A (false::true::(ps k++l)) (ps (m+2))) := by
  have h1 : run0 table (2*k) (B l (ps k++Q++ps m)) =
      some (B (ps k++l) (Q++ps m)) := by
    simpa only [List.append_assoc] using bSweep k l (Q++ps m)
  have h2 := bQ (ps k++l) (ps m)
  have h3 := bSweepEnd m (Q++(ps k++l))
  have h4 := aSweepOne m (Q++(ps k++l))
  have h5 := a10 (false::true::(ps k++l)) (ps (m+1))
  exact join0 (join0 (join0 (join0 h1 h2) h3) h4) h5

/-- Digits are little-endian: `10` is zero and `01` is one. The two
terminal markers and the empty tail are distinguished by the raw sweeps. -/
inductive Digits : List Bool → Prop where
  | nil : Digits []
  | endOne : Digits [true]
  | endTwo : Digits [true,true]
  | zero {x} : Digits x → Digits (D++x)
  | one {x} : Digits x → Digits (P++x)

theorem digits_ds (k : Nat) {x : List Bool} (h : Digits x) : Digits (ds k++x) := by
  induction k with
  | zero => exact h
  | succ k ih => simpa only [ds,List.append_assoc] using Digits.zero ih

/-- The three blank-left restart forms and the ordinary counter form. -/
inductive Inv : Z0 → Prop where
  | blank (n : Nat) : Inv (A [] (ps n))
  | blankOne (k m : Nat) : Inv (A [] (ps (k+1)++Q++ps m))
  | blankTwo (k m : Nat) : Inv (A [] (P++Q++ps k++Q++ps m))
  | single (n : Nat) : Inv (A [false,true] (ps n))
  | counter (n : Nat) {x : List Bool} : Digits x → Inv (A (false::true::false::x) (ps n))

def Continues (z : Z0) : Prop := ∃ t z', 0<t ∧ run0 table t z=some z' ∧ Inv z'

theorem prepend_run {n z y} (h : run0 table n z=some y) (hy : Continues y) : Continues z := by
  obtain ⟨t,z',ht,hr,hi⟩ := hy
  exact ⟨n+t,z',by omega,join0 h hr,hi⟩

theorem counter_shape (k : Nat) (x : List Bool) :
    false::true::(ps k++Q++x) = false::true::false::(ds k++P++x) := by
  rw [List.append_assoc,shift]
  change false::(ds k++(D++(P++x))) = _
  rw [←List.append_assoc (ds k) D (P++x),ds_snoc]
  simp only [ds,List.append_assoc]
  rfl

theorem counter_return (k m : Nat) {x : List Bool} (hx : Digits x) :
    Continues (B (Q++x) (ps k++Q++ps m)) := by
  have H := bGapReturn k m (Q++x)
  have H' : run0 table (2*k+3+(2*m+8)+2*m+2) (B (Q++x) (ps k++Q++ps m)) =
      some (A (false::true::false::(ds k++P++x)) (ps (m+2))) := by
    rw [←counter_shape]
    simpa only [List.append_assoc] using H
  have hd : Digits (ds k++P++x) := by
    simpa only [List.append_assoc] using digits_ds k (Digits.one hx)
  exact ⟨_,_,by omega,H',Inv.counter _ hd⟩

/-- Carry through arbitrarily many encoded one digits. The zero digit
case resets the preceding ones, and either terminal restarts on blank left. -/
theorem carry (k m : Nat) {x : List Bool} (hx : Digits x) :
    Continues (A (true::x) (ps k++Q++ps m)) := by
  induction hx generalizing k with
  | nil =>
    have H := a1 (ps k++Q++ps m)
    exact ⟨2,_,by decide,H,Inv.blankOne k m⟩
  | endOne =>
    exact prepend_run (a11 (ps k++Q++ps m)) (counter_return k m Digits.nil)
  | endTwo =>
    have H := join0 (a111 (ps k++Q++ps m)) (a1 (Q++(ps k++Q++ps m)))
    exact ⟨7,_,by decide,H,Inv.blankTwo k m⟩
  | @zero x hx ih =>
    exact prepend_run (a110 x (ps k++Q++ps m)) (counter_return k m hx)
  | @one x hx ih =>
    have H := a10 (true::x) (ps k++Q++ps m)
    exact prepend_run H (ih (k+1))

/-- First restart: all alternating right pairs, followed by a terminal
`11` turn, producing a single left one. -/
theorem blank_step (n : Nat) : Continues (A [] (ps n)) := by
  have h1 := join0 (aBlank (ps n)) (bSweepEnd n [true])
  have h2 := join0 h1 (aSweepOne n [true])
  have h3 := join0 h2 (a11 (ps (n+1)))
  have h4 := join0 h3 (bSweepEnd (n+1) Q)
  have h5 := join0 h4 (aSweepOne (n+1) Q)
  have h6 := join0 h5 (a10 [false,true] (ps (n+2)))
  exact ⟨_,_,by omega,h6,Inv.single (n+3)⟩

/-- Restart with one separator: the new counter has only zero digits
and the double-one terminal. -/
theorem blank_one_step (k m : Nat) : Continues (A [] (ps (k+1)++Q++ps m)) := by
  have H := join0 (aBlank (ps (k+1)++Q++ps m)) (bGapReturn (k+1) m [true])
  have hs : false::true::(ps (k+1)++[true]) = false::true::false::(ds k++[true,true]) := by
    rw [shift]
    rfl
  rw [hs] at H
  exact ⟨_,_,by omega,H,Inv.counter _ (digits_ds k Digits.endTwo)⟩

/-- Restart with two separators: two one digits and a single-one
terminal occur after the leading zero digits. -/
theorem blank_two_step (k m : Nat) : Continues (A [] (P++Q++ps k++Q++ps m)) := by
  have h1 := aBlank (P++(Q++(ps k++Q++ps m)))
  have h2 := bP [true] (Q++(ps k++Q++ps m))
  have h3 := bQ (P++[true]) (ps k++Q++ps m)
  have h4 := bGapReturn k m (Q++(P++[true]))
  have H := join0 (join0 (join0 h1 h2) h3) h4
  have H' : run0 table (1+2+3+(2*k+3+(2*m+8)+2*m+2)) (A [] (P++Q++ps k++Q++ps m)) =
      some (A (false::true::false::(ds k++P++P++[true])) (ps (m+2))) := by
    have hs := counter_shape k (P++[true])
    simp only [List.append_assoc] at hs H ⊢
    rw [hs] at H
    exact H
  have hd : Digits (ds k++P++P++[true]) := by
    simpa only [List.append_assoc] using digits_ds k (Digits.one (Digits.one Digits.endOne))
  exact ⟨_,_,by omega,H',Inv.counter _ hd⟩

theorem counter_step (n : Nat) {x : List Bool} (hx : Digits x) :
    Continues (A (false::true::false::x) (ps n)) := by
  have h1 := join0 (a0 (true::false::x) (ps n)) (bSweepEnd n (true::true::false::x))
  have h2 := join0 h1 (aSweepOne n (true::true::false::x))
  have h3 := join0 h2 (a1110 x (ps (n+1)))
  exact prepend_run h3 (carry 0 (n+1) hx)

theorem single_step (n : Nat) : Continues (A [false,true] (ps n)) := by
  have h1 := join0 (a0 [true] (ps n)) (bSweepEnd n [true,true])
  have h2 := join0 h1 (aSweepOne n [true,true])
  have h3 := join0 h2 (a111 (ps (n+1)))
  exact prepend_run h3 (carry 0 (n+1) Digits.nil)

theorem inv_step {z : Z0} (h : Inv z) : Continues z := by
  cases h with
  | blank n => exact blank_step n
  | blankOne k m => exact blank_one_step k m
  | blankTwo k m => exact blank_two_step k m
  | single n => exact single_step n
  | counter n hx => exact counter_step n hx

theorem arbitrary_live (N : Nat) : ∃ t z, N≤t ∧ run0 table t ⟨0,[],[]⟩=some z := by
  have H : ∀ N, ∃ t z, N≤t ∧ run0 table t ⟨0,[],[]⟩=some z ∧ Inv z := by
    intro n
    induction n with
    | zero => exact ⟨0,_,by omega,rfl,Inv.blank 0⟩
    | succ n ih =>
      obtain ⟨t,z,ht,hr,hi⟩ := ih
      obtain ⟨k,z',hk,hk',hi'⟩ := inv_step hi
      exact ⟨t+k,z',by omega,join0 hr hk',hi'⟩
  obtain ⟨t,z,ht,hr,_⟩ := H N
  exact ⟨t,z,ht,hr⟩

#print axioms bSweep
#print axioms aSweep
#print axioms carry
#print axioms inv_step
#print axioms arbitrary_live

open BB6Coverage.Agent50Zipper

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,hr⟩ := arbitrary_live n
  let s : Z := ⟨0,0,[],[]⟩
  have hz : (zrun table t s).map project = some z :=
    (run_project table t s).trans hr
  cases hZ : zrun table t s with
  | none => simp [hZ] at hz
  | some z' =>
      have H := zrun_sound table m hm t s z' hZ
      have hb : embed s = blank := BB6Coverage.Agent31Pump.start_embed
      rw [hb] at H
      rw [show t=n+(t-n) by omega,run_append] at H
      cases he : run m n blank with
      | none => simp [he] at H
      | some c => rfl

#print axioms never
end BB6.Agent25M81
