import Raw58RFTripleCore
import Raw58Live
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent4RF141
open BB6Coverage Agent31Pump Agent4RFTriple
-- 1RB0RF_1RC0LD_0RD1LE_1LD1RE_---0RA_0RC0RB
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

def A (r : List Bool) : Z0 := D (true::true::true::r)
inductive Digits : List Bool → Prop
  | last (b : Bool) : Digits [b,true]
  | block (b : Bool) (r : List Bool) : Digits r → Digits (b::true::true::r)

theorem pref111 (k : Nat) (r : List Bool) (h : Digits r) : Digits (rep [true,true,true] k ++ r) := by
  induction k with
  | zero => exact h
  | succ k ih => exact Digits.block true _ ih

theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (A [true,true]) := by rfl
theorem anchor (r : List Bool) : run0 table 3 (A r) = some (F 0 true r) := by rfl
theorem carry (k : Nat) (r : List Bool) : run0 table 5 (F k true (false::true::true::r)) = some (F (k+1) true r) := by rfl
theorem carryEnd (k : Nat) : run0 table 5 (F k true [false,true]) = some (F (k+1) false []) := by rfl

theorem move111 (k : Nat) (r : List Bool) :
    D (rep [true,true,true] k ++ true::true::true::r) = A (rep [true,true,true] k ++ r) := by
  unfold D A
  change (⟨3,[true,true],rep [true,true,true] k ++ ([true,true,true] ++ r)⟩ : Z0) =
    ⟨3,[true,true],[true,true,true] ++ (rep [true,true,true] k ++ r)⟩
  rw [← List.append_assoc,rep_snoc,List.append_assoc]

theorem stop (k : Nat) (r : List Bool) : run0 table (5+3*k) (F k true (true::r)) =
    some (A (rep [true,true,true] k ++ false::r)) := by
  have h : run0 table 5 (F k true (true::r)) =
    some ⟨3,rep [false,false,false] k ++ [true,true],true::true::true::false::r⟩ := by rfl
  have H := join0 h (sweep table (by intro L R; rfl) k (true::true::true::false::r))
  rw [move111] at H
  exact H

theorem overflow (k : Nat) : run0 table (7+3*k) (F k false []) =
    some (A (rep [true,true,true] k ++ [true,true])) := by
  have h : run0 table 7 (F k false []) =
    some ⟨3,rep [false,false,false] k ++ [true,true],[true,true,true,true,true]⟩ := by rfl
  have H := join0 h (sweep table (by intro L R; rfl) k [true,true,true,true,true])
  rw [move111] at H
  exact H

theorem returns (k : Nat) (r : List Bool) (hr : Digits r) :
    ∃ t s, 0 < t ∧ Digits s ∧ run0 table t (F k true r) = some (A s) := by
  induction hr generalizing k with
  | last b =>
    cases b with
    | false => exact ⟨_,_,by omega,pref111 (k+1) _ (Digits.last true),join0 (carryEnd k) (overflow (k+1))⟩
    | true => exact ⟨_,_,by omega,pref111 k _ (Digits.last false),stop k [true]⟩
  | block b r h ih =>
    cases b with
    | false =>
      obtain ⟨t,s,ht,hs,hh⟩ := ih (k+1)
      exact ⟨5+t,s,by omega,hs,join0 (carry k r) hh⟩
    | true => exact ⟨_,_,by omega,pref111 k _ (Digits.block false r h),stop k (true::true::r)⟩

theorem arbitrary (n : Nat) : ∃ t z, n ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some z := by
  have aux : ∀ n : Nat, ∃ t r, n ≤ t ∧ Digits r ∧ run0 table t ⟨0,[],[]⟩ = some (A r) := by
    intro n
    induction n with
    | zero => exact ⟨15,_,by omega,Digits.last true,entry⟩
    | succ n ih =>
      obtain ⟨t,r,ht,hr,hh⟩ := ih
      obtain ⟨u,s,hu,hs,hsr⟩ := returns 0 r hr
      exact ⟨t+(3+u),s,by omega,hs,join0 hh (join0 (anchor r) hsr)⟩
  obtain ⟨t,r,ht,_,hh⟩ := aux n
  exact ⟨t,A r,ht,hh⟩
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table arbitrary m hm
#print axioms never
end BB6Coverage.Agent4RF141
