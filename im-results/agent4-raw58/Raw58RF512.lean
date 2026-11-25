import Raw58RFTripleCore
import Raw58Live
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent4RF512
open BB6Coverage Agent31Pump
-- 1RB0RF_1RC---_0RD0LC_1LD1RE_1RF0RA_1LC1RE
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨true,true,4⟩)
  | _,_ => none

def A (r : List Bool) : Z0 := ⟨3,[true,true],true::true::true::r⟩
def F (k : Nat) (b : Bool) (r : List Bool) : Z0 := ⟨5,b::(rep [true,true] k ++ [false,false,true,true]),r⟩
inductive Digits : List Bool → Prop
  | nil : Digits []
  | pair (b : Bool) (r : List Bool) : Digits r → Digits (false::b::r)

theorem pref00 (k : Nat) (r : List Bool) (h : Digits r) : Digits (rep [false,false] k ++ r) := by
  induction k with
  | zero => exact h
  | succ k ih => exact Digits.pair false _ ih

theorem entry : run0 table 19 ⟨0,[],[]⟩ = some (A [false,true]) := by rfl
theorem anchor (r : List Bool) : run0 table 3 (A r) = some (F 0 true r) := by rfl
theorem carry (k : Nat) (b : Bool) (r : List Bool) : run0 table 2 (F k true (false::b::r)) = some (F (k+1) b r) := by rfl
theorem carryEnd (k : Nat) : run0 table 2 (F k true []) = some (F (k+1) false []) := by rfl

theorem zeroComm (k : Nat) (r : List Bool) :
    false::(rep [false,false] k ++ r) = rep [false,false] k ++ false::r := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [rep,List.cons_append,List.nil_append,List.cons.injEq,true_and] using ih

theorem stop (k : Nat) (r : List Bool) : run0 table (7+2*k) (F (k+1) false r) =
    some (A (rep [false,false] k ++ false::true::r)) := by
  have h1 : run0 table 1 (F (k+1) false r) =
      some ⟨2,rep [true,true] k ++ [true,true,false,false,true,true],true::r⟩ := by
    change some (⟨2, [true,true] ++ (rep [true,true] k ++ [false,false,true,true]),true::r⟩ : Z0) = _
    rw [← List.append_assoc,← rep_snoc,List.append_assoc]
    rfl
  have h2 : run0 table (2*k) ⟨2,rep [true,true] k ++ [true,true,false,false,true,true],true::r⟩ =
      some ⟨2,[true,true,false,false,true,true],rep [false,false] k ++ true::r⟩ := by
    simpa only [List.nil_append] using sweepL table 2 [] [] [true,true] [false,false] 2
      (by intro L R; rfl) k [true,true,false,false,true,true] (true::r)
  have h3 : run0 table 6 ⟨2,[true,true,false,false,true,true],rep [false,false] k ++ true::r⟩ =
      some (A (false::(rep [false,false] k ++ true::r))) := by rfl
  have H := join0 (join0 h1 h2) h3
  rw [zeroComm,show 1+2*k+6=7+2*k by omega] at H
  exact H

theorem returns (k : Nat) (b : Bool) (r : List Bool) (hr : Digits r) :
    ∃ t s, 0 < t ∧ Digits s ∧ run0 table t (F (k+1) b r) = some (A s) := by
  induction hr generalizing k b with
  | nil =>
    cases b with
    | false => exact ⟨_,_,by omega,pref00 k _ (Digits.pair true _ Digits.nil),stop k []⟩
    | true => exact ⟨_,_,by omega,pref00 (k+1) _ (Digits.pair true _ Digits.nil),join0 (carryEnd (k+1)) (stop (k+1) [])⟩
  | pair d r h ih =>
    cases b with
    | false => exact ⟨_,_,by omega,pref00 k _ (Digits.pair true _ (Digits.pair d r h)),stop k (false::d::r)⟩
    | true =>
      obtain ⟨t,s,ht,hs,hh⟩ := ih (k+1) d
      exact ⟨2+t,s,by omega,hs,join0 (carry (k+1) d r) hh⟩

theorem returnA (r : List Bool) (hr : Digits r) : ∃ t s, 0 < t ∧ Digits s ∧ run0 table t (A r) = some (A s) := by
  cases hr with
  | nil =>
    obtain ⟨t,s,ht,hs,hh⟩ := returns 0 false [] Digits.nil
    exact ⟨3+(2+t),s,by omega,hs,join0 (anchor []) (join0 (carryEnd 0) hh)⟩
  | pair b r h =>
    obtain ⟨t,s,ht,hs,hh⟩ := returns 0 b r h
    exact ⟨3+(2+t),s,by omega,hs,join0 (anchor _) (join0 (carry 0 b r) hh)⟩

theorem arbitrary (n : Nat) : ∃ t z, n ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some z := by
  have aux : ∀ n : Nat, ∃ t r, n ≤ t ∧ Digits r ∧ run0 table t ⟨0,[],[]⟩ = some (A r) := by
    intro n
    induction n with
    | zero => exact ⟨19,_,by omega,Digits.pair true _ Digits.nil,entry⟩
    | succ n ih =>
      obtain ⟨t,r,ht,hr,hh⟩ := ih
      obtain ⟨u,s,hu,hs,hsr⟩ := returnA r hr
      exact ⟨t+u,s,by omega,hs,join0 hh hsr⟩
  obtain ⟨t,r,ht,_,hh⟩ := aux n
  exact ⟨t,A r,ht,hh⟩
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table arbitrary m hm
#print axioms never
end BB6Coverage.Agent4RF512
