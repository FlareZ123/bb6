import Raw13Coupled6OneRACarry
namespace BB6Coverage.Agent31Pump.Raw13Coupled6OneRACarry
open BB6Coverage Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def digits : List Bool → List Bool
  | [] => []
  | b::bs => (if b then d1 else d0) ++ digits bs

def inc (w w' : List Bool) : Prop := ∃ j tail,
  w = rep one j ++ false::tail ∧ w' = rep zero j ++ true::tail

inductive Increments : Nat → List Bool → List Bool → Prop where
  | nil (w) : Increments 0 w w
  | cons {n w mid last} : inc w mid → Increments n mid last → Increments (n+1) w last

theorem split {m n : Nat} {w last : List Bool} (h : Increments (m+n) w last) :
    ∃ mid, Increments m w mid ∧ Increments n mid last := by
  induction m generalizing w with
  | zero => exact ⟨w,.nil w,by simpa using h⟩
  | succ m ih =>
    rw [show m+1+n=m+n+1 by omega] at h
    cases h with
    | cons hi hs =>
      obtain ⟨mid,hm,hn⟩ := ih hs
      exact ⟨mid,.cons hi hm,hn⟩

theorem digits_ones (j : Nat) (tail : List Bool) :
    digits (rep one j ++ tail) = rep d1 j ++ digits tail := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change d1 ++ digits (rep one j ++ tail) = d1 ++ rep d1 j ++ digits tail
    rw [ih,List.append_assoc]

theorem digits_zeros (j : Nat) (tail : List Bool) :
    digits (rep zero j ++ tail) = rep d0 j ++ digits tail := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change d0 ++ digits (rep zero j ++ tail) = d0 ++ rep d0 j ++ digits tail
    rw [ih,List.append_assoc]

theorem carry_inc (k : Nat) (L R : List Bool) {w w' : List Bool} (hi : inc w w') :
    ∃ t, 0<t ∧ run0 p t (A (false::L) (rep one k ++ digits w ++ R)) =
      some (A (rep zero k ++ true::L) (digits w' ++ R)) := by
  obtain ⟨j,tail,rfl,rfl⟩ := hi
  refine ⟨k+8*j+8,by omega,?_⟩
  simpa [digits_ones,digits_zeros,digits,List.append_assoc] using carry k j L (digits tail ++ R)

def Drain (k : Nat) : Prop := ∀ (L R : List Bool) {w w' : List Bool},
  Increments (2^k-1) w w' → ∃ t, run0 p t (A (rep zero (3*k) ++ L) (digits w ++ R)) =
    some (A L (rep one (3*k) ++ digits w' ++ R))

def Fill (k : Nat) : Prop := ∀ (L R : List Bool) {w w' : List Bool},
  Increments (2^k) w w' → ∃ t, 0<t ∧ run0 p t (A (false::L) (rep one (3*k) ++ digits w ++ R)) =
    some (A (true::L) (rep one (3*k) ++ digits w' ++ R))

theorem pow_positive (k : Nat) : 0<2^k := by exact Nat.two_pow_pos k

theorem fill_of_drain {k : Nat} (hd : Drain k) : Fill k := by
  intro L R w w' hs
  have hp := pow_positive k
  have eq : 2^k=2^k-1+1 := by omega
  rw [eq] at hs
  cases hs with
  | cons hi hn =>
    obtain ⟨a,ha,h⟩ := carry_inc (3*k) L R hi
    obtain ⟨b,hb⟩ := hd (true::L) R hn
    exact ⟨a+b,by omega,join0 h hb⟩

theorem drain_all (k : Nat) : Drain k := by
  induction k with
  | zero =>
    intro L R w w' hs
    cases hs
    exact ⟨0,rfl⟩
  | succ k ih =>
    intro L R w w' hs
    have hp := pow_positive k
    have eq : 2^(k+1)-1=(2^k-1)+2^k := by rw [Nat.pow_succ]; omega
    rw [eq] at hs
    obtain ⟨mid,hm,hn⟩ := split hs
    obtain ⟨a,ha⟩ := ih (false::false::false::L) R hm
    obtain ⟨b,hbp,hb⟩ := fill_of_drain ih (false::false::L) R hn
    have hc := left_triple L (rep one (3*k) ++ digits w' ++ R)
    have h := join0 (join0 ha hb) hc
    refine ⟨a+b+3,?_⟩
    have e : 3*(k+1)=3*k+3 := by omega
    rw [e,rep_add']
    simpa [rep,zero,one,List.append_assoc] using h

theorem fill_all (k : Nat) : Fill k := fill_of_drain (drain_all k)

theorem blank_advance (k : Nat) (R : List Bool) {w w' : List Bool} (hs : Increments (2^k) w w') :
    ∃ t, 0<t ∧ run0 p t (A [] (rep one (3*k) ++ digits w ++ R)) =
      some (A [] (rep one (3*(k+1)) ++ digits w' ++ R)) := by
  obtain ⟨a,ha,h⟩ := fill_all k [] R hs
  have hc (X : List Bool) : run0 p 3 (A [true] X) = some (A [] (true::true::true::X)) := by rfl
  have H := join0 h (hc (rep one (3*k) ++ digits w' ++ R))
  refine ⟨a+3,by omega,?_⟩
  have e : 3*(k+1)=3+3*k := by omega
  rw [e,rep_add']
  have hb : run0 p (a+3) (A [] (rep one (3*k) ++ digits w ++ R)) = run0 p (a+3) (A [false] (rep one (3*k) ++ digits w ++ R)) := by
    rw [show a+3=a+2+1 by omega]; exact blank_left _ _
  rw [hb]
  simpa [rep,one,List.append_assoc] using H

#print axioms drain_all
#print axioms fill_all
#print axioms blank_advance
end BB6Coverage.Agent31Pump.Raw13Coupled6OneRACarry
