import SweepPumping
import Raw58Live
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent4LFPair
open BB6Coverage Agent31Pump

-- v=false: LF294; v=true: LF314.
def table (v : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (if v then some ⟨true,false,3⟩ else some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def O : List Bool := [true,true]
def Z : List Bool := [false,false]
def P : List Bool := [false,true]
def C (n b : Nat) (R : List Bool) : Z0 := ⟨2,[false,true,true] ++ rep O n ++ rep P b,R⟩
def K (n b : Nat) (R : List Bool) : Z0 := ⟨2,[true,true,true] ++ rep O n ++ rep P b,R⟩
def pad (R : List Bool) : List Bool := false :: R.tail
def bt (v : Bool) : Nat := if v then 4 else 2

theorem zeroComm (n : Nat) (r : List Bool) : false::(rep Z n ++ r) = rep Z n ++ false::r := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [rep,Z,List.cons_append,List.nil_append,List.cons.injEq,true_and] using ih

theorem compressCore (v : Bool) (n b : Nat) (R : List Bool) (hR : R.headD false = false) :
    ∃ t, 0 < t ∧ run0 (table v) t (C n b R) = some ⟨1,O ++ rep P b,rep Z n ++ [false,false,true] ++ pad R⟩ := by
  have h1 : run0 (table v) 9 (C n b R) = some ⟨5,rep O n ++ rep P b,[false,false,true] ++ pad R⟩ := by
    cases v <;> cases R with
    | nil => rfl
    | cons x xs => cases x <;> first | rfl | simp at hR
  have h2 : run0 (table v) (2*n) ⟨5,rep O n ++ rep P b,[false,false,true] ++ pad R⟩ =
      some ⟨5,rep P b,rep Z n ++ [false,false,true] ++ pad R⟩ := by
    simpa only [List.nil_append,List.append_assoc] using sweepL (table v) 5 [] [] O Z 2
      (by intro L R; cases v <;> rfl) n (rep P b) ([false,false,true] ++ pad R)
  have h3 : run0 (table v) (2*b) ⟨5,rep P b,rep Z n ++ [false,false,true] ++ pad R⟩ =
      some ⟨5,[],rep P b ++ (rep Z n ++ [false,false,true] ++ pad R)⟩ := by
    simpa only [List.nil_append,List.append_nil,List.append_assoc] using sweepL (table v) 5 [] [] P P 2
      (by intro L R; cases v <;> rfl) b [] (rep Z n ++ [false,false,true] ++ pad R)
  have h4 : run0 (table v) 2 ⟨5,[],rep P b ++ (rep Z n ++ [false,false,true] ++ pad R)⟩ =
      some ⟨1,O,rep P b ++ (rep Z n ++ [false,false,true] ++ pad R)⟩ := by cases v <;> rfl
  have h5 : run0 (table v) (bt v*b) ⟨1,O,rep P b ++ (rep Z n ++ [false,false,true] ++ pad R)⟩ =
      some ⟨1,O ++ rep P b,rep Z n ++ [false,false,true] ++ pad R⟩ := by
    simpa only [List.nil_append,List.append_nil,List.append_assoc] using sweepR (table v) 1 O [] P P (bt v)
      (by intro L R; cases v <;> rfl) b [] (rep Z n ++ [false,false,true] ++ pad R)
  exact ⟨_,by omega,join0 (join0 (join0 (join0 h1 h2) h3) h4) h5⟩

theorem base (v : Bool) (b : Nat) (R : List Bool) (hR : R.headD false = false) :
    ∃ t, 0 < t ∧ run0 (table v) t (C 0 b R) = some (K 0 (b+1) (pad R)) := by
  obtain ⟨t,ht,h⟩ := compressCore v 0 b R hR
  have h2 : run0 (table v) (bt v+1) ⟨1,O ++ rep P b,rep Z 0 ++ [false,false,true] ++ pad R⟩ =
      some (K 0 (b+1) (pad R)) := by cases v <;> rfl
  exact ⟨_,by omega,join0 h h2⟩

theorem split (v : Bool) (n b : Nat) (R : List Bool) (hR : R.headD false = false) :
    ∃ t, 0 < t ∧ run0 (table v) t (C (n+1) b R) = some (C 0 (b+1) (rep Z n ++ [false,true] ++ pad R)) := by
  obtain ⟨t,ht,h⟩ := compressCore v (n+1) b R hR
  have he : rep Z (n+1) ++ [false,false,true] ++ pad R = [false,false,false,false] ++ rep Z n ++ true::pad R := by
    simp only [List.append_assoc]
    change false::false::(rep Z n ++ false::false::true::pad R) = false::false::false::false::(rep Z n ++ true::pad R)
    rw [← zeroComm n (false::true::pad R), ← zeroComm n (true::pad R)]
  rw [he] at h
  have h2 : run0 (table v) (bt v+1) ⟨1,O ++ rep P b,[false,false,false,false] ++ rep Z n ++ true::pad R⟩ =
      some (C 0 (b+1) (false::(rep Z n ++ true::pad R))) := by cases v <;> rfl
  rw [zeroComm] at h2
  exact ⟨_,by omega,join0 h (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using h2)⟩

def wall (d : Nat) (R : List Bool) : List Bool := rep Z d ++ [false,true] ++ R

theorem wallHead (d : Nat) (R : List Bool) : (wall d R).headD false = false := by
  cases d <;> rfl

theorem wallPad (d : Nat) (R : List Bool) : pad (wall d R) = wall d R := by
  cases d <;> rfl

theorem climb (v : Bool) (n : Nat)
    (lower : ∀ k, k < n → ∀ b R, R.headD false = false → ∃ t b', 0 < t ∧ run0 (table v) t (C k b R) = some (K k b' (pad R)))
    (d j b : Nat) (R : List Bool) (hn : j+d+1 = n) :
    ∃ t b', 0 < t ∧ run0 (table v) t (K j b (wall d R)) = some (K n b' R) := by
  induction d generalizing j b with
  | zero =>
    have h : run0 (table v) 2 (K j b (wall 0 R)) = some (K (j+1) b R) := by cases v <;> rfl
    have he : j+1 = n := by omega
    rw [he] at h
    exact ⟨2,b,by omega,h⟩
  | succ d ih =>
    have h1 : run0 (table v) 2 (K j b (wall (d+1) R)) = some (C (j+1) b (wall d R)) := by cases v <;> rfl
    obtain ⟨t,b',ht,h2⟩ := lower (j+1) (by omega) b (wall d R) (wallHead d R)
    rw [wallPad] at h2
    obtain ⟨u,b'',hu,h3⟩ := ih (j+1) b' (by omega)
    exact ⟨_,b'',by omega,join0 (join0 h1 h2) h3⟩

theorem resolve (v : Bool) (n : Nat) : ∀ b R, R.headD false = false →
    ∃ t b', 0 < t ∧ run0 (table v) t (C n b R) = some (K n b' (pad R)) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro b R hR
    cases n with
    | zero =>
      obtain ⟨t,ht,h⟩ := base v b R hR
      exact ⟨t,b+1,ht,h⟩
    | succ n =>
      obtain ⟨t,ht,h1⟩ := split v n b R hR
      change run0 (table v) t (C (n+1) b R) = some (C 0 (b+1) (wall n (pad R))) at h1
      obtain ⟨u,hu,h2⟩ := base v (b+1) (wall n (pad R)) (wallHead n (pad R))
      rw [wallPad] at h2
      obtain ⟨w,b',hw,h3⟩ := climb v (n+1) ih n 0 (b+1+1) (pad R) (by omega)
      exact ⟨_,b',by omega,join0 (join0 h1 h2) h3⟩

theorem grow (v : Bool) (n b : Nat) : ∃ t b', 0 < t ∧ run0 (table v) t (C n b []) = some (C (n+1) b' []) := by
  obtain ⟨t,b',ht,h1⟩ := resolve v n b [] rfl
  have h2 : run0 (table v) 2 (K n b' (pad [])) = some (C (n+1) b' []) := by cases v <;> rfl
  exact ⟨_,b',by omega,join0 h1 h2⟩

theorem arbitrary (v : Bool) (n : Nat) : ∃ t z, n ≤ t ∧ run0 (table v) t ⟨0,[],[]⟩ = some z := by
  have aux : ∀ k : Nat, ∃ t b, k ≤ t ∧ run0 (table v) t ⟨0,[],[]⟩ = some (C k b []) := by
    intro k
    induction k with
    | zero => exact ⟨2,0,by omega,by cases v <;> rfl⟩
    | succ k ih =>
      obtain ⟨t,b,ht,h1⟩ := ih
      obtain ⟨u,b',hu,h2⟩ := grow v k b
      exact ⟨_,b',by omega,join0 h1 h2⟩
  obtain ⟨t,b,ht,h⟩ := aux n
  exact ⟨t,C n b [],ht,h⟩

theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  Agent4Live.never_of_live (table v) (arbitrary v) m hm

#print axioms arbitrary
#print axioms never
end BB6Coverage.Agent4LFPair

namespace BB6Coverage.Agent4LF294
def table := Agent4LFPair.table false
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4LFPair.never false m hm
end BB6Coverage.Agent4LF294

namespace BB6Coverage.Agent4LF314
def table := Agent4LFPair.table true
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4LFPair.never true m hm
end BB6Coverage.Agent4LF314
