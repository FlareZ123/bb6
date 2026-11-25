import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw60LBBinary
open BB6Coverage BB6Coverage.Agent31Pump
inductive V | rb | rf deriving DecidableEq

def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some (match v with | .rb => ⟨false,true,1⟩ | .rf => ⟨false,true,5⟩))
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none
abbrev P : List Bool := [false,true]
abbrev U : List Bool := [false,true,false,true]
abbrev Z : List Bool := [false,true,false,false]
abbrev Q : List Bool := [true,false]
def o (n : Nat) := rep [true] n
def A (l r : List Bool) : Z0 := ⟨0,l,r⟩
def B (l r : List Bool) : Z0 := ⟨1,l,r⟩
def F (l r : List Bool) : Z0 := ⟨5,l,r⟩
def frame (a : Nat) := false::(o (4*a+3)++[false])
def Reach (v : V) (c d : Z0) : Prop := ∃ t, run0 (table v) t c = some d

theorem trans {v : V} {a b c : Z0} (h : Reach v a b) (g : Reach v b c) : Reach v a c := by
  obtain ⟨i,hi⟩ := h
  obtain ⟨j,hj⟩ := g
  exact ⟨i+j,join0 hi hj⟩

theorem rep_add (P : List Bool) (a b : Nat) : rep P (a+b) = rep P a ++ rep P b := by
  induction a with
  | zero => simp [rep]
  | succ a ih =>
    rw [show a+1+b=(a+b)+1 by omega]
    simp only [rep,ih,List.append_assoc]

theorem o_add (a b : Nat) : o (a+b) = o a ++ o b := rep_add [true] a b

theorem pairs (a : Nat) : rep P (2*a) = rep U a := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [show 2*(a+1)=2+2*a by omega,rep_add,ih]
    rfl

theorem zero (v : V) (a : Nat) (R : List Bool) : run0 (table v) 6 (A (frame a) (Z++R)) = some (A (frame (a+1)) R) := by
  unfold frame
  rw [show 4*(a+1)+3=4+(4*a+3) by omega,o_add 4 (4*a+3)]
  cases v <;> rfl

theorem one (v : V) (a : Nat) (R : List Bool) : run0 (table v) 6 (A (frame a) (U++R)) = some (A (o (4*a+8)++[false]) R) := by
  unfold frame
  rw [show 4*a+8=5+(4*a+3) by omega,o_add 5 (4*a+3)]
  cases v <;> rfl

theorem pair_ones (n : Nat) : rep [true,true] n = o (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1)=2+2*n by omega,o_add]
    simp only [rep,ih]; rfl

theorem f_sweep (v : V) (n : Nat) (L R : List Bool) : run0 (table v) (2*n) (F (o (2*n)++L) R) = some (F L (rep P n++R)) := by
  have H := sweepL (table v) 5 [] [] [true,true] P 2 (by intro l r; cases v <;> rfl) n L R
  simpa only [F,List.nil_append,pair_ones] using H

theorem b_sweep (v : V) (n : Nat) (L R : List Bool) : run0 (table v) (2*n) (B (o (2*n)++L) R) = some (B L (rep Q n++R)) := by
  have H := sweepL (table v) 1 [] [] [true,true] Q 2 (by intro l r; cases v <;> rfl) n L R
  simpa only [B,List.nil_append,pair_ones] using H

def hop (v : V) : Nat := match v with | .rb => 6 | .rf => 8

theorem f_one (v : V) (R : List Bool) : run0 (table v) (hop v) (F [false] (U++R)) = some (A [true,true,true,true,false] R) := by cases v <;> rfl

theorem f_zero (v : V) (R : List Bool) : run0 (table v) (hop v) (F [false] (Z++R)) = some (A (frame 0) R) := by cases v <;> rfl

theorem f_begin (v : V) (R : List Bool) : run0 (table v) (hop v) (F [] (Z++R)) = some (A (frame 0) R) := by cases v <;> rfl

theorem rewind (v : V) (a : Nat) (R : List Bool) : Reach v (A (o (4*a+8)++[false]) R) (F [false] (U++rep U a++Z++R)) := by
  have h1 : run0 (table v) 2 (A (o (4*a+8)++[false]) R) = some (F (o (4*a+6)++[false]) (false::false::R)) := by rfl
  have h2 := f_sweep v (2*a+3) [false] (false::false::R)
  have h2' : run0 (table v) (2*(2*a+3)) (F (o (4*a+6)++[false]) (false::false::R)) = some (F [false] (U++rep U a++Z++R)) := by
    rw [show 4*a+6=2*(2*a+3) by omega]
    have eq : rep P (2*a+3) ++ false::false::R = U++rep U a++Z++R := by
      rw [show 2*a+3=2+2*a+1 by omega,rep_add,rep_add,pairs]
      simp only [List.append_assoc]; rfl
    rw [← eq]
    exact h2
  exact trans ⟨2,h1⟩ ⟨_,h2'⟩

theorem borrow (v : V) (a : Nat) (R : List Bool) : Reach v (A (frame a) (U++R)) (A (frame 0) (rep U a++Z++R)) := by
  have h1 := one v a R
  have h2 := rewind v a R
  have h3 := f_one v (rep U a++Z++R)
  have h4 : run0 (table v) 4 (A [true,true,true,true,false] (rep U a++Z++R)) = some (F [false] (Z++rep U a++Z++R)) := by cases v <;> rfl
  have h5 := f_zero v (rep U a++Z++R)
  exact trans ⟨6,h1⟩ (trans (by simpa only [List.append_assoc] using h2) (trans ⟨hop v,h3⟩ (trans ⟨4,by simpa only [List.append_assoc] using h4⟩ ⟨hop v,h5⟩)))

theorem clear (v : V) (a b : Nat) (R : List Bool) : Reach v (A (frame a) (rep U b++R)) (A (frame (a+b)) R) := by
  have aux : ∀ n b a, a+b=n → ∀ R, Reach v (A (frame a) (rep U b++R)) (A (frame (a+b)) R) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro b
      induction b with
      | zero => intro a _ R; exact ⟨0,rfl⟩
      | succ b ib =>
        intro a hn R
        have h1 := borrow v a (rep U b++R)
        have h2 := ih a (by omega) a 0 (by omega) (Z++rep U b++R)
        have h3 := zero v a (rep U b++R)
        have h4 := ib (a+1) (by omega) R
        have H := trans (by simpa only [rep,List.append_assoc] using h1) (trans (by simpa only [Nat.zero_add,List.append_assoc] using h2) (trans ⟨6,h3⟩ h4))
        simpa only [rep,List.append_assoc,show a+1+b=a+(b+1) by omega] using H
  exact aux (a+b) b a rfl R

theorem finish (v : V) (n : Nat) : Reach v (A (frame (n+1)) []) (F [] (Z++rep U (n+1)++Z)) := by
  have h1 : run0 (table v) 7 (A (frame (n+1)) []) = some (A (o (4*n+11)++[false]) []) := by
    unfold frame
    rw [show 4*(n+1)+3=4*n+7 by omega,show 4*n+11=4+(4*n+7) by omega,o_add 4 (4*n+7)]
    cases v <;> rfl
  have h2 : run0 (table v) 1 (A (o (4*n+11)++[false]) []) = some (B (o (4*n+10)++[false]) [false]) := by rfl
  have h3 := b_sweep v (2*n+5) [false] [false]
  have h3' : run0 (table v) (2*(2*n+5)) (B (o (4*n+10)++[false]) [false]) = some (B [false] (Q++Q++rep Q (2*n+3)++[false])) := by
    rw [show 4*n+10=2*(2*n+5) by omega]
    rw [show 2*n+5=2*n+3+1+1 by omega] at h3 ⊢
    simpa only [rep,List.append_assoc] using h3
  have h4 : run0 (table v) 5 (B [false] (Q++Q++rep Q (2*n+3)++[false])) = some (A [true,true,true,true] (rep U (n+1)++Z)) := by
    have e : (false::(rep Q (2*n+3)++[false])) = rep U (n+1)++Z := by
      have rot : ∀ k, false::(rep Q k++[false]) = rep P k++[false,false] := by
        intro k; induction k with
        | zero => rfl
        | succ k ih =>
          change false::true::false::(rep Q k++[false]) = rep P (k+1)++[false,false]
          rw [ih]; rfl
      rw [rot,show 2*n+3=2*(n+1)+1 by omega,rep_add,pairs]; rw [List.append_assoc]; rfl
    rw [← e]
    cases v <;> rfl
  have h5 : run0 (table v) 4 (A [true,true,true,true] (rep U (n+1)++Z)) = some (F [] (Z++rep U (n+1)++Z)) := by cases v <;> rfl
  exact trans ⟨7,h1⟩ (trans ⟨1,h2⟩ (trans ⟨_,by simpa only [List.append_assoc] using h3'⟩ (trans ⟨5,h4⟩ ⟨4,by simpa only [List.append_assoc] using h5⟩)))

def family (n : Nat) := F [] (Z++rep U n++Z)
def entryTime (v : V) := match v with | .rb => 40 | .rf => 42
theorem entry (v : V) : run0 (table v) (entryTime v) ⟨0,[],[]⟩ = some (family 0) := by cases v <;> rfl

theorem grow (v : V) (n : Nat) : Reach v (family n) (family (n+1)) := by
  have h1 := f_begin v (rep U n++Z)
  have h2 := clear v 0 n Z
  have h3 := zero v n []
  have h4 := finish v n
  exact trans ⟨hop v,by simpa only [family,List.append_assoc] using h1⟩ (trans (by simpa only [Nat.zero_add] using h2) (trans ⟨6,by simpa only [List.append_nil] using h3⟩ h4))

noncomputable def cost (v : V) (n : Nat) : Nat := Classical.choose (grow v n)
theorem growth (v : V) (n : Nat) : run0 (table v) (cost v n) (family n) = some (family (n+1)) := Classical.choose_spec (grow v n)
theorem positive (v : V) (n : Nat) : 0 < cost v n := by
  have len (n : Nat) : (rep U n).length = 4*n := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [rep,List.length_append,ih,show U.length=4 by rfl]; omega
  by_cases h : cost v n = 0
  · have H := growth v n
    rw [h,run0] at H
    have E := congrArg (fun c : Z0 => c.r.length) (Option.some.inj H)
    simp only [family,F,List.length_append,len] at E
    omega
  · omega

theorem never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) family (entryTime v) (cost v) (entry v) (positive v) (growth v) m hm

namespace M24
def table := BB6.Agent1Raw60LBBinary.table .rb
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6.Agent1Raw60LBBinary.never .rb m hm
end M24
namespace M28
def table := BB6.Agent1Raw60LBBinary.table .rf
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6.Agent1Raw60LBBinary.never .rf m hm
end M28
#print axioms clear
#print axioms growth
#print axioms never
end BB6.Agent1Raw60LBBinary
