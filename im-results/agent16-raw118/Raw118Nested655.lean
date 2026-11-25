import RecursiveCounterCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent16Raw118Nested.M655
open BB6Coverage Agent31Pump Agent40Recursive Agent40Independent

-- Exact one-hole row 655: 1RB1LA_1RC1RB_0RD0LA_1LD1RE_0RF0LE_0RB---
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | _,_ => none

def O (n : Nat) : List Bool := List.replicate n true
def Z (n : Nat) : List Bool := List.replicate n false

theorem O_add (a b : Nat) : O (a+b) = O a ++ O b := List.replicate_append_replicate.symm
theorem Z_add (a b : Nat) : Z (a+b) = Z a ++ Z b := List.replicate_append_replicate.symm

theorem O_snoc (n : Nat) (L : List Bool) : O n ++ true::L = O (n+1) ++ L := by
  rw [O_add]; simp [List.append_assoc,O]

theorem Z_snoc (n : Nat) (L : List Bool) : Z n ++ false::L = Z (n+1) ++ L := by
  rw [Z_add]; simp [List.append_assoc,Z]

theorem awalk (k : Nat) (L R : List Bool) :
    run0 table k ⟨0,O k ++ L,R⟩ = some ⟨0,L,O k ++ R⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h : run0 table 1 ⟨0,true::(O k ++ L),R⟩ = some ⟨0,O k ++ L,true::R⟩ := by rfl
    have hh := join0 h (ih (true::R))
    rw [O_snoc] at hh
    rw [show k+1=1+k by omega] at ⊢
    simpa only [Nat.add_comm 1 k, O, List.replicate_succ,List.cons_append] using hh

def B (L R : List Bool) : Z0 := ⟨1,R.headD false::L,R.tail⟩

theorem bwalk (k : Nat) (L R : List Bool) (b : Bool) :
    run0 table (k+1) (B L (O k ++ false::b::R)) = some ⟨2,b::(O (k+1) ++ L),R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    have h : run0 table 1 (B L (O (k+1) ++ false::b::R)) = some (B (true::L) (O k ++ false::b::R)) := by rfl
    have hh := join0 h (ih (true::L))
    rw [O_snoc] at hh
    simpa only [Nat.add_comm 1 (k+1)] using hh

theorem cstep (k : Nat) (L R : List Bool) (b : Bool) :
    PositiveRun table ⟨2,true::(O k ++ false::L),b::R⟩ ⟨2,b::(O (k+2) ++ L),R⟩ := by
  have h1 : run0 table 1 ⟨2,true::(O k ++ false::L),b::R⟩ = some ⟨0,O k ++ false::L,false::b::R⟩ := by rfl
  have h2 := awalk k (false::L) (false::b::R)
  have h3 : run0 table 1 ⟨0,false::L,O k ++ false::b::R⟩ = some (B (true::L) (O k ++ false::b::R)) := by rfl
  have h4 := bwalk k (true::L) R b
  rw [O_snoc] at h4
  exact ⟨1+k+1+(k+1),by omega,join0 (join0 (join0 h1 h2) h3) h4⟩

theorem cwalk (j k : Nat) (L R : List Bool) :
    PositiveRun table ⟨2,true::(O k ++ Z (j+1) ++ L),O j ++ false::R⟩ ⟨2,false::(O (k+2*(j+1)) ++ L),R⟩ := by
  induction j generalizing k with
  | zero => simpa [O,Z] using cstep k L R false
  | succ j ih =>
    have h := cstep k (Z (j+1) ++ L) (O j ++ false::R) true
    have h' := ih (k+2)
    rw [List.append_assoc] at h'
    have H := h.trans h'
    simpa only [O,Z,List.replicate_succ,List.cons_append,List.append_assoc,show k + 2 + 2*(j+1) = k+2*(j+1+1) by omega] using H

theorem ewalk (k : Nat) (L R : List Bool) :
    run0 table k ⟨4,O k ++ L,R⟩ = some ⟨4,L,Z k ++ R⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h : run0 table 1 ⟨4,true::(O k ++ L),R⟩ = some ⟨4,O k ++ L,false::R⟩ := by rfl
    have hh := join0 h (ih (false::R))
    rw [Z_snoc] at hh
    simpa only [Nat.add_comm 1 k, O, List.replicate_succ,List.cons_append] using hh

def F (n : Nat) (S R : List Bool) : Z0 :=
  ⟨5,Z (n+2) ++ S,false::(O (n+1) ++ R)⟩

theorem reset (k : Nat) (S R : List Bool) :
    PositiveRun table ⟨3,false::false::(O (k+1) ++ false::S),R⟩
      ⟨5,false::false::S,Z (k+1) ++ true::R⟩ := by
  have h1 : run0 table 3 ⟨3,false::false::(O (k+1) ++ false::S),R⟩ =
      some ⟨4,O (k+2) ++ false::S,true::R⟩ := by rfl
  have h2 := ewalk (k+2) (false::S) (true::R)
  have h3 : run0 table 1 ⟨4,false::S,Z (k+2) ++ true::R⟩ =
      some ⟨5,false::false::S,Z (k+1) ++ true::R⟩ := by rfl
  exact ⟨3+(k+2)+1,by omega,join0 (join0 h1 h2) h3⟩

theorem seed (S R : List Bool) :
    PositiveRun table ⟨5,false::false::S,false::false::false::R⟩
      (F 0 (false::S) R) := ⟨9,by decide,by rfl⟩

theorem toReset (n : Nat) (S R : List Bool) :
    PositiveRun table (F n S (false::false::R))
      ⟨5,false::false::S,Z (2*n+3) ++ true::R⟩ := by
  have h1 : run0 table 2 (F n S (false::false::R)) =
      some ⟨2,true::(O 1 ++ Z (n+1) ++ false::S),O n ++ false::false::R⟩ := by
    unfold F
    rw [List.append_assoc, Z_snoc]
    rfl
  have h2 := cwalk n 1 (false::S) (false::R)
  have h3 : run0 table 1 ⟨2,false::(O (1+2*(n+1)) ++ false::S),false::R⟩ =
      some ⟨3,false::false::(O (1+2*(n+1)) ++ false::S),R⟩ := by rfl
  have h4 := reset (2*n+2) S R
  rw [show 1+2*(n+1)=2*n+2+1 by omega] at h3 h2
  exact (show PositiveRun table _ _ from ⟨2,by decide,h1⟩).trans (h2.trans ((show PositiveRun table _ _ from ⟨1,by decide,h3⟩).trans h4))

theorem F_merge (n : Nat) (S R : List Bool) : F n (false::S) (true::R) = F (n+1) S R := by
  unfold F
  rw [Z_snoc,O_snoc]

/-- Nested restoration for arbitrary untouched suffixes. The subcalls have
    strictly smaller run counters; this is an unbounded inductive argument. -/
theorem restore (n : Nat) (S R : List Bool) :
    PositiveRun table (F n S (false::false::R)) (F (n+1) S R) := by
  induction n using Nat.strongRecOn generalizing S R with
  | ind n ih =>
    have h := toReset n S R
    have hseed := seed S (Z (2*n) ++ true::R)
    have hs : Z (2*n+3) ++ true::R = false::false::false::(Z (2*n) ++ true::R) := by
      rw [show 2*n+3=3+2*n by omega,Z_add,List.append_assoc]; rfl
    rw [hs] at h
    have first := h.trans hseed
    have walk : ∀ k j, j+k=n → ∀ T : List Bool,
        ∃ t, run0 table t (F j (false::S) (Z (2*k) ++ true::T)) = some (F (n+1) S T) := by
      intro k
      induction k with
      | zero =>
        intro j hj T
        have eq : j=n := by omega
        subst j
        exact ⟨0,by simpa [Z,run0] using congrArg some (F_merge n S T)⟩
      | succ k hk =>
        intro j hj T
        have hstep := ih j (by omega) (false::S) (Z (2*k) ++ true::T)
        have eq : Z (2*(k+1)) ++ true::T = false::false::(Z (2*k) ++ true::T) := by
          rw [show 2*(k+1)=2+2*k by omega,Z_add,List.append_assoc]; rfl
        obtain ⟨t,ht,hstep⟩ := hstep
        rw [← eq] at hstep
        obtain ⟨v,hv⟩ := hk (j+1) (by omega) T
        exact ⟨t+v,join0 hstep hv⟩
    obtain ⟨t,ht,hfirst⟩ := first
    obtain ⟨v,hv⟩ := walk n 0 (by omega) R
    exact ⟨t+v,by omega,join0 hfirst hv⟩

theorem bwalk_empty (k : Nat) (L : List Bool) :
    run0 table (k+1) (B L (O k ++ [false])) = some ⟨2,false::(O (k+1) ++ L),[]⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    have h : run0 table 1 (B L (O (k+1) ++ [false])) = some (B (true::L) (O k ++ [false])) := by rfl
    have hh := join0 h (ih (true::L))
    rw [O_snoc] at hh
    simpa only [Nat.add_comm 1 (k+1)] using hh

theorem cstep_empty (k : Nat) (L : List Bool) :
    PositiveRun table ⟨2,true::(O k ++ false::L),[]⟩ ⟨2,false::(O (k+2) ++ L),[]⟩ := by
  have h1 : run0 table 1 ⟨2,true::(O k ++ false::L),[]⟩ = some ⟨0,O k ++ false::L,[false]⟩ := by rfl
  have h2 := awalk k (false::L) [false]
  have h3 : run0 table 1 ⟨0,false::L,O k ++ [false]⟩ = some (B (true::L) (O k ++ [false])) := by rfl
  have h4 := bwalk_empty k (true::L)
  rw [O_snoc] at h4
  exact ⟨1+k+1+(k+1),by omega,join0 (join0 (join0 h1 h2) h3) h4⟩

theorem cwalk_empty (j k : Nat) (L : List Bool) :
    PositiveRun table ⟨2,true::(O k ++ Z (j+1) ++ L),O j⟩ ⟨2,false::(O (k+2*(j+1)) ++ L),[]⟩ := by
  induction j generalizing k with
  | zero => simpa [O,Z] using cstep_empty k L
  | succ j ih =>
    have h := cstep k (Z (j+1) ++ L) (O j) true
    have h' := ih (k+2)
    rw [List.append_assoc] at h'
    have H := h.trans h'
    simpa only [O,Z,List.replicate_succ,List.cons_append,List.append_assoc,show k + 2 + 2*(j+1) = k+2*(j+1+1) by omega] using H

theorem reset_empty (n : Nat) (S : List Bool) :
    PositiveRun table (F n S []) ⟨5,false::false::S,Z (2*n+3) ++ [true]⟩ := by
  have h1 : run0 table 2 (F n S []) =
      some ⟨2,true::(O 1 ++ Z (n+1) ++ false::S),O n⟩ := by
    unfold F
    rw [List.append_assoc, Z_snoc]
    simp only [List.append_nil]
    rfl
  have h2 := cwalk_empty n 1 (false::S)
  have h3 : run0 table 1 ⟨2,false::(O (1+2*(n+1)) ++ false::S),[]⟩ =
      some ⟨3,false::false::(O (1+2*(n+1)) ++ false::S),[]⟩ := by rfl
  have h4 := reset (2*n+2) S []
  rw [show 1+2*(n+1)=2*n+2+1 by omega] at h3 h2
  exact (show PositiveRun table _ _ from ⟨2,by decide,h1⟩).trans (h2.trans ((show PositiveRun table _ _ from ⟨1,by decide,h3⟩).trans h4))

theorem blank_grow (n : Nat) (S : List Bool) :
    PositiveRun table (F n S []) (F (n+1) S []) := by
  have h := reset_empty n S
  have hs : Z (2*n+3) ++ [true] = false::false::false::(Z (2*n) ++ [true]) := by
    rw [show 2*n+3=3+2*n by omega,Z_add,List.append_assoc]; rfl
  rw [hs] at h
  have first := h.trans (seed S (Z (2*n) ++ [true]))
  have walk : ∀ k j, j+k=n → ∃ t, run0 table t (F j (false::S) (Z (2*k) ++ [true])) = some (F (n+1) S []) := by
    intro k
    induction k with
    | zero =>
      intro j hj
      have eq : j=n := by omega
      subst j
      exact ⟨0,by simpa [Z,run0] using congrArg some (F_merge n S [])⟩
    | succ k hk =>
      intro j hj
      have hstep := restore j (false::S) (Z (2*k) ++ [true])
      have eq : Z (2*(k+1)) ++ [true] = false::false::(Z (2*k) ++ [true]) := by
        rw [show 2*(k+1)=2+2*k by omega,Z_add,List.append_assoc]; rfl
      obtain ⟨t,ht,hstep⟩ := hstep
      rw [← eq] at hstep
      obtain ⟨v,hv⟩ := hk (j+1) (by omega)
      exact ⟨t+v,join0 hstep hv⟩
  obtain ⟨t,ht,hfirst⟩ := first
  obtain ⟨v,hv⟩ := walk n 0 (by omega)
  exact ⟨t+v,by omega,join0 hfirst hv⟩

def suffix : List Bool := [false,true,false,true,false,false]
def Inv (z : Z0) : Prop := ∃ n, z = F n suffix []
theorem entry : ∃ t z, run0 table t ⟨0,[],[]⟩ = some z ∧ Inv z :=
  ⟨24,F 0 suffix [],by rfl,⟨0,rfl⟩⟩
theorem closed : ∀ z, Inv z → ∃ k z', 0 < k ∧ run0 table k z = some z' ∧ Inv z' := by
  rintro z ⟨n,rfl⟩
  obtain ⟨k,hk,h⟩ := blank_grow n suffix
  exact ⟨k,F (n+1) suffix [],hk,h,⟨n+1,rfl⟩⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_closed table Inv entry closed m hm
#print axioms restore
#print axioms blank_grow
#print axioms entry
#print axioms closed
#print axioms never
end BB6Coverage.Agent16Raw118Nested.M655
