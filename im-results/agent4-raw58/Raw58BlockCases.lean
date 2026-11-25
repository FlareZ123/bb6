import Raw58Live
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent4BlockCases.M1481
open BB6Coverage Agent31Pump
-- 1RB0RC_1RC0RF_0RD0RB_1LD1RE_---0RA_0RC0LD
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def A (r : List Bool) : Z0 := ⟨0,[true,false,true,true],r⟩
def C (k : Nat) (r : List Bool) : Z0 := ⟨2,r.headD false :: false :: false :: (rep [false,false,false] k ++ [true,true]),r.tail⟩
def D (lp : List Bool) (k : Nat) (r : List Bool) : Z0 := ⟨3,lp ++ rep [false,false,false] k ++ [true,true],r⟩
theorem entry : run0 table 7 ⟨0,[],[]⟩ = some (A []) := by rfl
theorem anchor (r : List Bool) : run0 table 1 (A r) = some (C 0 r) := by rfl

theorem oneComm (k : Nat) (r : List Bool) :
    true :: (rep [true,true,true] k ++ r) = rep [true,true,true] k ++ true::r := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [rep,List.cons_append,List.nil_append,List.cons.injEq,true_and] using ih

theorem clear (lp : List Bool)
    (one : ∀ L R, run0 table 3 ⟨3,lp++[false,false,false]++L,[]++R⟩ = some ⟨3,lp++L,[]++[true,true,true]++R⟩)
    (k : Nat) (r : List Bool) : run0 table (3*k) (D lp k r) = some (D lp 0 (rep [true,true,true] k ++ r)) := by
  simpa only [D,rep,List.nil_append,List.append_nil] using sweepL table 3 lp [] [false,false,false] [true,true,true] 3 one k [true,true] r

theorem empty (k : Nat) :
    run0 table (7+3*k) (C k []) = some (A (rep [true,true,true] k ++ true::true::[])) := by
  have h1 : run0 table 1 (C k []) = some (D [false,false,false,false] k ([])) := by rfl
  have h2 := clear [false,false,false,false] (by intro L R; rfl) k ([])
  have h3 : run0 table 6 (D [false,false,false,false] 0 (rep [true,true,true] k ++ ([]))) = some (A (true::true::(rep [true,true,true] k ++ []))) := by rfl
  have h := join0 (join0 h1 h2) h3
  simp only [oneComm] at h
  rw [show 1+3*k+6=7+3*k by omega] at h
  exact h

theorem stop (k : Nat) (r : List Bool) :
    run0 table (9+3*k) (C k (true::true::true::r)) = some (A (rep [true,true,true] k ++ true::true::false::r)) := by
  have h1 : run0 table 3 (C k (true::true::true::r)) = some (D [false,false,false,false] k (false::r)) := by rfl
  have h2 := clear [false,false,false,false] (by intro L R; rfl) k (false::r)
  have h3 : run0 table 6 (D [false,false,false,false] 0 (rep [true,true,true] k ++ (false::r))) = some (A (true::true::(rep [true,true,true] k ++ false::r))) := by rfl
  have h := join0 (join0 h1 h2) h3
  simp only [oneComm] at h
  rw [show 3+3*k+6=9+3*k by omega] at h
  exact h

theorem carry (k : Nat) (r : List Bool) :
    run0 table 3 (C k (true::true::false::r)) = some (C (k+1) r) := by rfl

theorem terminal (k : Nat) : run0 table 3 (C k [true,true]) = some (C (k+1) []) := by rfl
inductive Code : List Bool → Prop
  | nil : Code []
  | short : Code [true,true]
  | block (b : Bool) (r : List Bool) : Code r → Code (true::true::b::r)

theorem wordPrefix (k : Nat) (r : List Bool) (h : Code r) : Code (rep [true,true,true] k ++ r) := by
  induction k with
  | zero => exact h
  | succ k ih => exact Code.block true _ ih

theorem returns (k : Nat) (r : List Bool) (hr : Code r) : ∃ t s, 0 < t ∧ Code s ∧ run0 table t (C k r) = some (A s) := by
  induction hr generalizing k with
  | nil => exact ⟨_,_,by omega,wordPrefix k _ Code.short,empty k⟩
  | short => exact ⟨_,_,by omega,wordPrefix (k+1) _ Code.short,join0 (terminal k) (empty (k+1))⟩
  | block b r h ih =>
    cases b with
    | false =>
      obtain ⟨t,s,ht,hs,hret⟩ := ih (k+1)
      exact ⟨3+t,s,by omega,hs,join0 (carry k r) hret⟩
    | true => exact ⟨_,_,by omega,wordPrefix k _ (Code.block false r h),stop k r⟩

theorem arbitrary (n : Nat) : ∃ t r, n ≤ t ∧ Code r ∧ run0 table t ⟨0,[],[]⟩ = some (A r) := by
  induction n with
  | zero => exact ⟨7,[],by omega,Code.nil,entry⟩
  | succ n ih =>
    obtain ⟨t,r,ht,hr,hh⟩ := ih
    obtain ⟨u,s,hu,hs,hret⟩ := returns 0 r hr
    exact ⟨t+(1+u),s,by omega,hs,join0 hh (join0 (anchor r) hret)⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table (fun n => by
    obtain ⟨t,r,ht,_,hr⟩ := arbitrary n
    exact ⟨t,A r,ht,hr⟩) m hm
#print axioms never
end BB6Coverage.Agent4BlockCases.M1481
namespace BB6Coverage.Agent4BlockCases.M1511
open BB6Coverage Agent31Pump
-- 1RB0RC_1RC---_0RD0RF_1LD1RE_0RC0RA_0RE0LD
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨false,true,4⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def A (r : List Bool) : Z0 := ⟨0,[true,false,true,true],r⟩
def C (k : Nat) (r : List Bool) : Z0 := ⟨2,r.headD false :: false :: false :: (rep [false,false,false,false] k ++ [true,true]),r.tail⟩
def D (lp : List Bool) (k : Nat) (r : List Bool) : Z0 := ⟨3,lp ++ rep [false,false,false,false] k ++ [true,true],r⟩
theorem entry : run0 table 7 ⟨0,[],[]⟩ = some (A []) := by rfl
theorem anchor (r : List Bool) : run0 table 1 (A r) = some (C 0 r) := by rfl

theorem oneComm (k : Nat) (r : List Bool) :
    true :: (rep [true,true,true,true] k ++ r) = rep [true,true,true,true] k ++ true::r := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [rep,List.cons_append,List.nil_append,List.cons.injEq,true_and] using ih

theorem clear (lp : List Bool)
    (one : ∀ L R, run0 table 4 ⟨3,lp++[false,false,false,false]++L,[]++R⟩ = some ⟨3,lp++L,[]++[true,true,true,true]++R⟩)
    (k : Nat) (r : List Bool) : run0 table (4*k) (D lp k r) = some (D lp 0 (rep [true,true,true,true] k ++ r)) := by
  simpa only [D,rep,List.nil_append,List.append_nil] using sweepL table 3 lp [] [false,false,false,false] [true,true,true,true] 4 one k [true,true] r

theorem empty (k : Nat) :
    run0 table (7+4*k) (C k []) = some (A (rep [true,true,true,true] k ++ true::true::[])) := by
  have h1 : run0 table 1 (C k []) = some (D [false,false,false,false] k ([])) := by rfl
  have h2 := clear [false,false,false,false] (by intro L R; rfl) k ([])
  have h3 : run0 table 6 (D [false,false,false,false] 0 (rep [true,true,true,true] k ++ ([]))) = some (A (true::true::(rep [true,true,true,true] k ++ []))) := by rfl
  have h := join0 (join0 h1 h2) h3
  simp only [oneComm] at h
  rw [show 1+4*k+6=7+4*k by omega] at h
  exact h

theorem stop (k : Nat) (r : List Bool) :
    run0 table (7+4*k) (C k (true::true::r)) = some (A (rep [true,true,true,true] k ++ true::false::r)) := by
  have h1 : run0 table 2 (C k (true::true::r)) = some (D [false,false,false] k (false::r)) := by rfl
  have h2 := clear [false,false,false] (by intro L R; rfl) k (false::r)
  have h3 : run0 table 5 (D [false,false,false] 0 (rep [true,true,true,true] k ++ (false::r))) = some (A (true::(rep [true,true,true,true] k ++ false::r))) := by rfl
  have h := join0 (join0 h1 h2) h3
  simp only [oneComm] at h
  rw [show 2+4*k+5=7+4*k by omega] at h
  exact h

theorem terminalOne (k : Nat) :
    run0 table (13+4*k) (C k [true]) = some (A (rep [true,true,true,true] k ++ true::true::true::true::true::[])) := by
  have h1 : run0 table 4 (C k [true]) = some (D [false,false,false,false,false,false,false] k ([])) := by rfl
  have h2 := clear [false,false,false,false,false,false,false] (by intro L R; rfl) k ([])
  have h3 : run0 table 9 (D [false,false,false,false,false,false,false] 0 (rep [true,true,true,true] k ++ ([]))) = some (A (true::true::true::true::true::(rep [true,true,true,true] k ++ []))) := by rfl
  have h := join0 (join0 h1 h2) h3
  simp only [oneComm] at h
  rw [show 4+4*k+9=13+4*k by omega] at h
  exact h

theorem terminalZero (k : Nat) :
    run0 table (13+4*k) (C k [true,false]) = some (A (rep [true,true,true,true] k ++ true::true::true::true::true::[])) := by
  have h1 : run0 table 4 (C k [true,false]) = some (D [false,false,false,false,false,false,false] k ([])) := by rfl
  have h2 := clear [false,false,false,false,false,false,false] (by intro L R; rfl) k ([])
  have h3 : run0 table 9 (D [false,false,false,false,false,false,false] 0 (rep [true,true,true,true] k ++ ([]))) = some (A (true::true::true::true::true::(rep [true,true,true,true] k ++ []))) := by rfl
  have h := join0 (join0 h1 h2) h3
  simp only [oneComm] at h
  rw [show 4+4*k+9=13+4*k by omega] at h
  exact h

theorem carry (k : Nat) (r : List Bool) :
    run0 table 4 (C k (true::false::true::true::r)) = some (C (k+1) r) := by rfl

inductive Code : List Bool → Prop
  | nil : Code []
  | one : Code [true]
  | pair (b : Bool) : Code [true,b]
  | block (b : Bool) (r : List Bool) : Code r → Code (true::b::true::true::r)

theorem wordPrefix (k : Nat) (r : List Bool) (h : Code r) : Code (rep [true,true,true,true] k ++ r) := by
  induction k with
  | zero => exact h
  | succ k ih => exact Code.block true _ ih

theorem returns (k : Nat) (r : List Bool) (hr : Code r) : ∃ t s, 0 < t ∧ Code s ∧ run0 table t (C k r) = some (A s) := by
  induction hr generalizing k with
  | nil => exact ⟨_,_,by omega,wordPrefix k _ (Code.pair true),empty k⟩
  | one => exact ⟨_,_,by omega,wordPrefix k _ (Code.block true _ Code.one),terminalOne k⟩
  | pair b =>
    cases b with
    | false => exact ⟨_,_,by omega,wordPrefix k _ (Code.block true _ Code.one),terminalZero k⟩
    | true => exact ⟨_,_,by omega,wordPrefix k _ (Code.pair false),stop k []⟩
  | block b r h ih =>
    cases b with
    | false =>
      obtain ⟨t,s,ht,hs,hret⟩ := ih (k+1)
      exact ⟨4+t,s,by omega,hs,join0 (carry k r) hret⟩
    | true => exact ⟨_,_,by omega,wordPrefix k _ (Code.block false r h),stop k (true::true::r)⟩

theorem arbitrary (n : Nat) : ∃ t r, n ≤ t ∧ Code r ∧ run0 table t ⟨0,[],[]⟩ = some (A r) := by
  induction n with
  | zero => exact ⟨7,[],by omega,Code.nil,entry⟩
  | succ n ih =>
    obtain ⟨t,r,ht,hr,hh⟩ := ih
    obtain ⟨u,s,hu,hs,hret⟩ := returns 0 r hr
    exact ⟨t+(1+u),s,by omega,hs,join0 hh (join0 (anchor r) hret)⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table (fun n => by
    obtain ⟨t,r,ht,_,hr⟩ := arbitrary n
    exact ⟨t,A r,ht,hr⟩) m hm
#print axioms never
end BB6Coverage.Agent4BlockCases.M1511
namespace BB6Coverage.Agent4BlockCases.M1512
open BB6Coverage Agent31Pump
-- 1RB0RC_1RC---_0RD0RF_1LD1RE_0RD0RA_0RE0LD
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,3⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨false,true,4⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def A (r : List Bool) : Z0 := ⟨0,[true,false,true,true],r⟩
def C (k : Nat) (r : List Bool) : Z0 := ⟨2,r.headD false :: false :: false :: (rep [false,false,false,false] k ++ [true,true]),r.tail⟩
def D (lp : List Bool) (k : Nat) (r : List Bool) : Z0 := ⟨3,lp ++ rep [false,false,false,false] k ++ [true,true],r⟩
theorem entry : run0 table 7 ⟨0,[],[]⟩ = some (A []) := by rfl
theorem anchor (r : List Bool) : run0 table 1 (A r) = some (C 0 r) := by rfl

theorem oneComm (k : Nat) (r : List Bool) :
    true :: (rep [true,true,true,true] k ++ r) = rep [true,true,true,true] k ++ true::r := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [rep,List.cons_append,List.nil_append,List.cons.injEq,true_and] using ih

theorem clear (lp : List Bool)
    (one : ∀ L R, run0 table 4 ⟨3,lp++[false,false,false,false]++L,[]++R⟩ = some ⟨3,lp++L,[]++[true,true,true,true]++R⟩)
    (k : Nat) (r : List Bool) : run0 table (4*k) (D lp k r) = some (D lp 0 (rep [true,true,true,true] k ++ r)) := by
  simpa only [D,rep,List.nil_append,List.append_nil] using sweepL table 3 lp [] [false,false,false,false] [true,true,true,true] 4 one k [true,true] r

theorem empty (k : Nat) :
    run0 table (7+4*k) (C k []) = some (A (rep [true,true,true,true] k ++ true::true::[])) := by
  have h1 : run0 table 1 (C k []) = some (D [false,false,false,false] k ([])) := by rfl
  have h2 := clear [false,false,false,false] (by intro L R; rfl) k ([])
  have h3 : run0 table 6 (D [false,false,false,false] 0 (rep [true,true,true,true] k ++ ([]))) = some (A (true::true::(rep [true,true,true,true] k ++ []))) := by rfl
  have h := join0 (join0 h1 h2) h3
  simp only [oneComm] at h
  rw [show 1+4*k+6=7+4*k by omega] at h
  exact h

theorem stop (k : Nat) (r : List Bool) :
    run0 table (7+4*k) (C k (true::true::r)) = some (A (rep [true,true,true,true] k ++ true::false::r)) := by
  have h1 : run0 table 2 (C k (true::true::r)) = some (D [false,false,false] k (false::r)) := by rfl
  have h2 := clear [false,false,false] (by intro L R; rfl) k (false::r)
  have h3 : run0 table 5 (D [false,false,false] 0 (rep [true,true,true,true] k ++ (false::r))) = some (A (true::(rep [true,true,true,true] k ++ false::r))) := by rfl
  have h := join0 (join0 h1 h2) h3
  simp only [oneComm] at h
  rw [show 2+4*k+5=7+4*k by omega] at h
  exact h

theorem terminalZero (k : Nat) :
    run0 table (11+4*k) (C k [true,false]) = some (A (rep [true,true,true,true] k ++ true::true::true::true::[])) := by
  have h1 : run0 table 3 (C k [true,false]) = some (D [false,false,false,false,false,false] k ([])) := by rfl
  have h2 := clear [false,false,false,false,false,false] (by intro L R; rfl) k ([])
  have h3 : run0 table 8 (D [false,false,false,false,false,false] 0 (rep [true,true,true,true] k ++ ([]))) = some (A (true::true::true::true::(rep [true,true,true,true] k ++ []))) := by rfl
  have h := join0 (join0 h1 h2) h3
  simp only [oneComm] at h
  rw [show 3+4*k+8=11+4*k by omega] at h
  exact h

theorem carry (k : Nat) (r : List Bool) :
    run0 table 4 (C k (true::false::true::true::r)) = some (C (k+1) r) := by rfl

inductive Code : List Bool → Prop
  | nil : Code []
  | pair (b : Bool) : Code [true,b]
  | block (b : Bool) (r : List Bool) : Code r → Code (true::b::true::true::r)

theorem wordPrefix (k : Nat) (r : List Bool) (h : Code r) : Code (rep [true,true,true,true] k ++ r) := by
  induction k with
  | zero => exact h
  | succ k ih => exact Code.block true _ ih

theorem returns (k : Nat) (r : List Bool) (hr : Code r) : ∃ t s, 0 < t ∧ Code s ∧ run0 table t (C k r) = some (A s) := by
  induction hr generalizing k with
  | nil => exact ⟨_,_,by omega,wordPrefix k _ (Code.pair true),empty k⟩
  | pair b =>
    cases b with
    | false => exact ⟨_,_,by omega,wordPrefix k _ (Code.block true _ Code.nil),terminalZero k⟩
    | true => exact ⟨_,_,by omega,wordPrefix k _ (Code.pair false),stop k []⟩
  | block b r h ih =>
    cases b with
    | false =>
      obtain ⟨t,s,ht,hs,hret⟩ := ih (k+1)
      exact ⟨4+t,s,by omega,hs,join0 (carry k r) hret⟩
    | true => exact ⟨_,_,by omega,wordPrefix k _ (Code.block false r h),stop k (true::true::r)⟩

theorem arbitrary (n : Nat) : ∃ t r, n ≤ t ∧ Code r ∧ run0 table t ⟨0,[],[]⟩ = some (A r) := by
  induction n with
  | zero => exact ⟨7,[],by omega,Code.nil,entry⟩
  | succ n ih =>
    obtain ⟨t,r,ht,hr,hh⟩ := ih
    obtain ⟨u,s,hu,hs,hret⟩ := returns 0 r hr
    exact ⟨t+(1+u),s,by omega,hs,join0 hh (join0 (anchor r) hret)⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table (fun n => by
    obtain ⟨t,r,ht,_,hr⟩ := arbitrary n
    exact ⟨t,A r,ht,hr⟩) m hm
#print axioms never
end BB6Coverage.Agent4BlockCases.M1512
