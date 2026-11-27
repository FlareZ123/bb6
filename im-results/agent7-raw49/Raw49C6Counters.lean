import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw49C6Counters
open BB6Coverage BB6Coverage.Agent31Pump

theorem rep_add (P : List Bool) (a b : Nat) : rep P (a+b) = rep P a ++ rep P b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [Nat.succ_add]; simp only [rep,ih,List.append_assoc]

namespace M608
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,false,2⟩)
  | _,_ => none

def A (L R : List Bool) : Z0 := ⟨0,L,R⟩
def U := rep [true,true]
def R := rep [true,false]
def V := rep [false,true]
def T : Nat → List Bool
  | 0 => []
  | n+1 => false::true::true::U n

theorem rone (L X : List Bool) : run0 table 2 (A (false::L) (true::false::X)) = some (A (false::true::true::L) X) := by rfl

theorem rscan (n : Nat) (L X : List Bool) : run0 table (2*n) (A (false::L) (R n++X)) = some (A (false::(U n++L)) X) := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h := join0 (rone L (R n++X)) (ih (true::true::L))
    have hr : U n ++ true::true::L = U (n+1) ++ L := by
      unfold U
      rw [rep_add]
      simp only [rep,List.append_assoc,List.cons_append,List.nil_append]
    rw [hr,show 2+2*n=2*(n+1) by omega] at h
    exact h

theorem rfirst (X : List Bool) : run0 table 2 (A [] (true::false::X)) = some (A [false,true,true] X) := by rfl

theorem scan (n : Nat) (X : List Bool) : run0 table (2*n) (A [] (R n++X)) = some (A (T n) X) := by
  cases n with
  | zero => rfl
  | succ n =>
    have h := join0 (rfirst (R n++X)) (rscan n [true,true] X)
    have hr : U n ++ [true,true] = true::true::U n := by
      exact rep_snoc [true,true] n
    rw [hr,show 2+2*n=2*(n+1) by omega] at h
    exact h

theorem gapTurn (n : Nat) (X : List Bool) : run0 table 3 (A (T n) (false::true::X)) = some (A (U (n+1)) (false::X)) := by
  cases n <;> rfl

theorem endTurn (n : Nat) : run0 table 7 (A (T n) []) = some (A (U (n+1)) [false,true]) := by
  cases n <;> rfl

theorem lastOne (n : Nat) : run0 table 2 (A (T n) [true]) = some (A (T (n+1)) []) := by
  cases n <;> rfl

theorem lone (L X : List Bool) : run0 table 4 (A (true::true::true::true::L) X) = some (A L (false::true::false::true::X)) := by rfl

theorem lscan (k j : Nat) (X : List Bool) : run0 table (4*k) (A (U (2*k+j)) X) = some (A (U j) (V (2*k)++X)) := by
  induction k generalizing X with
  | zero => simp [U,V,rep,run0]
  | succ k ih =>
    have h := join0 (lone (U (2*k+j)) X) (ih (false::true::false::true::X))
    have hr : V (2*k) ++ false::true::false::true::X = V (2*(k+1)) ++ X := by
      unfold V
      rw [show 2*(k+1)=2*k+2 by omega,rep_add]
      simp only [rep,List.append_assoc,List.cons_append,List.nil_append]
    rw [hr,show 4+4*k=4*(k+1) by omega] at h
    rw [show 2*(k+1)+j=(2*k+j)+2 by omega]
    exact h

theorem finish (X : List Bool) : run0 table 3 (A [true,true] X) = some (A [] (true::false::true::X)) := by rfl

theorem rotateV (n : Nat) : true::(V n) = R n ++ [true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change true::false::true::V n = true::false::(R n++[true])
    rw [← ih]

def G (k l : Nat) : Z0 := A [] (R (2*k)++V l)
def O (k : Nat) : Z0 := A [] (R (2*k)++[true])

theorem gap (k l : Nat) : run0 table (8*k+6) (G k (l+1)) = some (G (k+1) l) := by
  have h1 := scan (2*k) (V (l+1))
  have h := join0 h1 (gapTurn (2*k) (V l))
  have h := join0 h (lscan k 1 (false::V l))
  have h := join0 h (finish (V (2*k)++false::V l))
  have hr : true::false::true::(V (2*k)++false::V l) = R (2*(k+1))++V l := by
    have he := rotateV (2*k)
    change (true::false::((true::V (2*k))++false::V l)) = _
    rw [he]
    unfold R
    rw [show 2*(k+1)=1+(2*k+1) by omega,rep_add,rep_add]
    simp only [rep,List.append_assoc,List.cons_append,List.nil_append]
  rw [hr,show 2*(2*k)+3+4*k+3=8*k+6 by omega] at h
  exact h

theorem even (k : Nat) : run0 table (8*k+10) (G k 0) = some (O (k+1)) := by
  have h := join0 (scan (2*k) []) (endTurn (2*k))
  have h := join0 h (lscan k 1 [false,true])
  have h := join0 h (finish (V (2*k)++[false,true]))
  have hr : true::false::true::(V (2*k)++[false,true]) = R (2*(k+1))++[true] := by
    have he := rotateV (2*k)
    change (true::false::((true::V (2*k))++[false,true])) = _
    rw [he]
    unfold R
    rw [show 2*(k+1)=1+(2*k+1) by omega,rep_add,rep_add]
    simp only [rep,List.append_assoc,List.cons_append,List.nil_append]
  rw [hr,show 2*(2*k)+7+4*k+3=8*k+10 by omega] at h
  simpa only [G,O,V,rep,List.append_nil] using h

theorem odd (k : Nat) : run0 table (8*k+13) (O k) = some (G 0 (2*k+3)) := by
  have h := join0 (scan (2*k) [true]) (lastOne (2*k))
  have h := join0 h (endTurn (2*k+1))
  have hs := lscan (k+1) 0 [false,true]
  rw [show 2*(k+1)+0=2*k+1+1 by omega] at hs
  have h := join0 h hs
  have hr : V (2*(k+1))++[false,true] = V (2*k+3) := by
    unfold V
    rw [show 2*k+3=2*(k+1)+1 by omega,rep_add]
    rfl
  rw [hr,show 2*(2*k)+2+7+4*(k+1)=8*k+13 by omega] at h
  exact h

def gapCost (k : Nat) : Nat → Nat
  | 0 => 0
  | l+1 => 8*k+6+gapCost (k+1) l

theorem gapAll (k l : Nat) : run0 table (gapCost k l) (G k l) = some (G (k+l) 0) := by
  induction l generalizing k with
  | zero => rfl
  | succ l ih =>
    have h := join0 (gap k l) (ih (k+1))
    rw [show k+1+l=k+(l+1) by omega] at h
    exact h

def cost (k : Nat) : Nat := 8*k+13+gapCost 0 (2*k+3)+(8*(2*k+3)+10)
theorem growth (k : Nat) : run0 table (cost k) (O k) = some (O (2*k+4)) := by
  have h := join0 (odd k) (gapAll 0 (2*k+3))
  simp only [Nat.zero_add] at h
  have h := join0 h (even (2*k+3))
  rw [show 2*k+3+1=2*k+4 by omega] at h
  exact h

theorem entry : run0 table 10 ⟨0,[],[]⟩ = some (O 1) := by rfl
#print axioms growth
#print axioms entry
def index : Nat → Nat
  | 0 => 1
  | n+1 => 2*index n+4

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table (fun n => O (index n)) 10 (fun n => cost (index n)) entry
    (by intro n; unfold cost; omega) (fun n => growth (index n)) m hm
#print axioms never
end M608

namespace M613
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨false,false,4⟩)
  | 4,true => some (some ⟨true,true,1⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | _,_ => none

def B (L R : List Bool) : Z0 := ⟨1,L,R⟩
def E (L R : List Bool) : Z0 := ⟨4,L,R⟩
def enc : List Bool → List Bool
  | [] => [true,false,true]
  | b::bs => b::false::b::false::enc bs

def inc : List Bool → List Bool
  | [] => [false]
  | false::bs => true::bs
  | true::bs => false::inc bs

def scan (L : List Bool) : List Bool → Z0
  | [] => B (true::L) [false,true]
  | b::bs => B (b::L) (false::b::false::enc bs)

def zeros4 : List Bool := [false,false,false,false]

theorem enter (L bs : List Bool) : run0 table 1 (E (true::L) (enc bs)) = some (scan (true::L) bs) := by
  cases bs <;> rfl

theorem carryOne (L bs : List Bool) : run0 table 4 (scan L (true::bs)) = some (scan (zeros4++L) bs) := by
  cases bs <;> rfl

theorem carryEnd (L : List Bool) : run0 table 4 (scan L []) = some (B (false::(zeros4++L)) []) := by rfl

theorem setBit (L bs : List Bool) : run0 table 7 (scan L (false::bs)) = some (E L (enc (true::bs))) := by rfl

theorem extend (L : List Bool) : run0 table 7 (B (false::L) []) = some (E L (enc [])) := by rfl

theorem back (L X : List Bool) : run0 table 4 (E (zeros4++L) X) = some (E L (zeros4++X)) := by rfl

def carryCost : List Bool → Nat
  | [] => 15
  | false::_ => 7
  | true::bs => 4+carryCost bs+4

theorem carry (L bs : List Bool) : run0 table (carryCost bs) (scan L bs) = some (E L (enc (inc bs))) := by
  induction bs generalizing L with
  | nil => exact join0 (join0 (carryEnd L) (extend (zeros4++L))) (back L (enc []))
  | cons b bs ih =>
    cases b with
    | false => exact setBit L bs
    | true => exact join0 (join0 (carryOne L bs) (ih (zeros4++L))) (back L (enc (inc bs)))

def sec (bs : List Bool) := E [true] (enc bs)
theorem growth (bs : List Bool) : run0 table (1+carryCost bs) (sec bs) = some (sec (inc bs)) :=
  join0 (enter [] bs) (carry [true] bs)

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (sec []) := by rfl
#print axioms growth
#print axioms entry
def index : Nat → List Bool
  | 0 => []
  | n+1 => inc (index n)

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table (fun n => sec (index n)) 8 (fun n => 1+carryCost (index n)) entry
    (by intro n; omega) (fun n => growth (index n)) m hm
#print axioms never
end M613

namespace M600
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,true,1⟩)
  | _,_ => none

def B (L R : List Bool) : Z0 := ⟨1,L,R⟩
def C (L R : List Bool) : Z0 := ⟨2,L,R⟩
def E (L R : List Bool) : Z0 := ⟨4,L,R⟩

-- The first cell is odd. All odd cells on the right are zero.
inductive RO : List Bool → Prop where
  | nil : RO []
  | last : RO [false]
  | pair (b : Bool) (r : List Bool) (h : RO r) : RO (false::b::r)

-- Left pairs are reversed (odd then even). An odd 1 has even 1 to its left.
inductive LO : List Bool → Prop where
  | nil : LO []
  | last : LO [false]
  | pair (a b : Bool) (l : List Bool) (h : a = false ∨ b = true) (hl : LO l) : LO (a::b::l)

theorem ro_tail2 {r : List Bool} (h : RO r) : RO r.tail.tail := by
  cases h with
  | nil | last => exact RO.nil
  | pair b r hr => exact hr

theorem ro_prefix {r : List Bool} (h : RO r.tail) : RO (false::r) := by
  cases r with
  | nil => exact RO.last
  | cons a r => exact RO.pair a r h

theorem ro_head {r : List Bool} (h : RO r) : r.headD false = false := by cases h <;> rfl

inductive Safe : Z0 → Prop where
  | b (l r : List Bool) (hl : LO l.tail) (hr : RO r) : Safe (B l r)
  | c (l r : List Bool) (hl : LO l) (hr : RO r.tail) : Safe (C (false::true::l) r)
  | e (l r : List Bool) (hl : LO l) (hr : RO r.tail) : Safe (E l r)

def first : Z0 := B [] [false,true,false,true,false,true,false,true,false,true,false]
theorem entry : run0 table 58 ⟨0,[],[]⟩ = some first := by rfl
theorem firstSafe : Safe first := by
  apply Safe.b [] _ LO.nil
  repeat first | exact RO.last | exact RO.nil | apply RO.pair

theorem bzeroNil (r : List Bool) (h : RO r) :
    run0 table 1 (B [] r) = some (C [false,true] r.tail) := by
  cases h <;> rfl

theorem bzero (l r : List Bool) (h : RO r) :
    run0 table 1 (B (false::l) r) = some (C (false::true::l) r.tail) := by
  cases h <;> rfl

theorem bone (l r : List Bool) (h : RO r) :
    run0 table 2 (B (true::l) r) = some (B (r.tail.headD false::true::true::l) r.tail.tail) := by
  cases h <;> rfl

theorem cone (l r : List Bool) (h : RO r) :
    run0 table 2 (C (false::true::l) (true::r)) = some (C (false::true::false::true::l) r.tail) := by
  cases h <;> rfl

theorem czero (l r : List Bool) :
    run0 table 6 (C (false::true::l) (false::r)) = some (E l (true::false::true::r)) := by rfl

theorem czeroNil (l : List Bool) :
    run0 table 6 (C (false::true::l) []) = some (E l [true,false,true]) := by rfl

theorem ezero (l r : List Bool) :
    run0 table 1 (E (false::l) r) = some (B l (false::r)) := by rfl

theorem ezeroNil (r : List Bool) :
    run0 table 1 (E [] r) = some (B [] (false::r)) := by rfl

theorem eone (l r : List Bool) :
    run0 table 2 (E (true::true::l) r) = some (E l (false::false::r)) := by rfl

theorem progress {z : Z0} (h : Safe z) : ∃ k : Nat, 0<k ∧ ∃ z', Safe z' ∧ run0 table k z = some z' := by
  cases h with
  | b l r hl hr =>
    cases l with
    | nil =>
      exact ⟨1,by decide,_,Safe.c [] r.tail LO.nil (ro_tail2 hr),bzeroNil r hr⟩
    | cons a l =>
      cases a with
      | false => exact ⟨1,by decide,_,Safe.c l r.tail hl (ro_tail2 hr),bzero l r hr⟩
      | true =>
        exact ⟨2,by decide,_,Safe.b (r.tail.headD false::true::true::l) r.tail.tail (LO.pair true true l (Or.inr rfl) hl) (ro_tail2 hr),bone l r hr⟩
  | c l r hl hr =>
    cases r with
    | nil => exact ⟨6,by decide,_,Safe.e l [true,false,true] hl (RO.pair true [] RO.nil),czeroNil l⟩
    | cons a r =>
      cases a with
      | false => exact ⟨6,by decide,_,Safe.e l (true::false::true::r) hl (RO.pair true r hr),czero l r⟩
      | true => exact ⟨2,by decide,_,Safe.c _ _ (LO.pair false true l (Or.inl rfl) hl) (ro_tail2 hr),cone l r hr⟩
  | e l r hl hr =>
    cases hl with
    | nil => exact ⟨1,by decide,_,Safe.b [] _ LO.nil (ro_prefix hr),ezeroNil r⟩
    | last => exact ⟨1,by decide,_,Safe.b [] _ LO.nil (ro_prefix hr),ezero [] r⟩
    | pair a b l hab hl =>
      cases a with
      | false => exact ⟨1,by decide,_,Safe.b (b::l) _ hl (ro_prefix hr),ezero (b::l) r⟩
      | true =>
        have hb : b=true := hab.resolve_left (by decide)
        subst b
        exact ⟨2,by decide,_,Safe.e l (false::false::r) hl (ro_prefix hr),eone l r⟩

theorem livePrefixes (n : Nat) : ∃ t, n≤t ∧ ∃ z, Safe z ∧ run0 table t ⟨0,[],[]⟩ = some z := by
  induction n with
  | zero => exact ⟨58,by decide,first,firstSafe,entry⟩
  | succ n ih =>
    obtain ⟨t,ht,z,hz,hr⟩ := ih
    obtain ⟨k,hk,z',hz',hk'⟩ := progress hz
    exact ⟨t+k,by omega,z',hz',join0 hr hk'⟩
#print axioms progress
#print axioms livePrefixes
open BB6Coverage.Agent50Zipper

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,ht,z,_,hr⟩ := livePrefixes n
  have hz : (zrun table t start).map project = some z := (run_project table t start).trans hr
  cases h : zrun table t start with
  | none => simp [h] at hz
  | some zz =>
    have H := zrun_sound table m hm t start zz h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl
#print axioms never
end M600
end BB6.Agent7Raw49C6Counters
