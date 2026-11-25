import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw41.LB0LC3
open BB6Coverage BB6Coverage.Agent31Pump
-- 1RB0LB_1RC0LC_0RD0LE_1LD1RA_0RA0LF_0RC---
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,0⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | _,_ => none

def Q : List Bool := [false,false,false,true]
def X : List Bool := [true,false,false,true]
def P : List Bool := [true,true,true,false]
def code : List Bool → List Bool
  | [] => []
  | b::bs => (if b then X else Q) ++ code bs

def family (bits : List Bool) : Z0 := ⟨4,[false],Q++code bits⟩
def scan (k : Nat) (bits : List Bool) : Z0 := ⟨0,[false,true,false]++rep P k++[true,true,false],[false,false,true]++code bits⟩
def resume (k : Nat) (bits : List Bool) : Z0 := ⟨4,[true,false]++rep P k++[true,true,false],Q++code bits⟩
theorem entry : run0 table 33 ⟨0,[],[]⟩ = some (family [true]) := by rfl

theorem startEmpty : run0 table 24 (family []) = some (family [true]) := by rfl
theorem startTrue (bs : List Bool) : run0 table 14 (family (true::bs)) = some (family (false::bs)) := by rfl
theorem startFalse (bs : List Bool) : run0 table 5 (family (false::bs)) = some (scan 0 bs) := by rfl

theorem scanFalse (k : Nat) (bs : List Bool) : run0 table 4 (scan k (false::bs)) = some (scan (k+1) bs) := by rfl
theorem scanTrue (k : Nat) (bs : List Bool) : run0 table 13 (scan k (true::bs)) = some (resume k (false::bs)) := by rfl
theorem scanEmpty (k : Nat) : run0 table 13 (scan k []) = some (resume (k+1) []) := by rfl

theorem resumeMore (k : Nat) (bs : List Bool) : run0 table 10 (resume (k+1) bs) = some (resume k (true::bs)) := by rfl
theorem resumeDone (bs : List Bool) : run0 table 10 (resume 0 bs) = some (family (true::bs)) := by rfl

theorem resume_progress (k : Nat) (bs : List Bool) :
    ∃ t out, 0 < t ∧ run0 table t (resume k bs) = some (family out) := by
  induction k generalizing bs with
  | zero => exact ⟨10,true::bs,by decide,resumeDone bs⟩
  | succ k ih =>
    obtain ⟨t,out,ht,hr⟩ := ih (true::bs)
    exact ⟨10+t,out,by omega,join0 (resumeMore k bs) hr⟩

theorem scan_progress (k : Nat) (bs : List Bool) :
    ∃ t out, 0 < t ∧ run0 table t (scan k bs) = some (family out) := by
  induction bs generalizing k with
  | nil =>
    obtain ⟨t,out,ht,hr⟩ := resume_progress (k+1) []
    exact ⟨13+t,out,by omega,join0 (scanEmpty k) hr⟩
  | cons b bs ih =>
    cases b with
    | false =>
      obtain ⟨t,out,ht,hr⟩ := ih (k+1)
      exact ⟨4+t,out,by omega,join0 (scanFalse k bs) hr⟩
    | true =>
      obtain ⟨t,out,ht,hr⟩ := resume_progress k (false::bs)
      exact ⟨13+t,out,by omega,join0 (scanTrue k bs) hr⟩

theorem progress (bs : List Bool) : ∃ t out, 0 < t ∧ run0 table t (family bs) = some (family out) := by
  cases bs with
  | nil => exact ⟨24,[true],by decide,startEmpty⟩
  | cons b bs =>
    cases b with
    | false =>
      obtain ⟨t,out,ht,hr⟩ := scan_progress 0 bs
      exact ⟨5+t,out,by omega,join0 (startFalse bs) hr⟩
    | true => exact ⟨14,false::bs,by decide,startTrue bs⟩

/-- A positively recurrent invariant over any index type suffices; no explicit
formula for a counter's successive words is required. -/
theorem never_of_returns {α : Type} (p : PartialMachine) (f : α → Z0) (a : α)
    (e : Nat) (first : run0 p e ⟨0,[],[]⟩ = some (f a))
    (returns : ∀ a, ∃ t b, 0 < t ∧ run0 p t (f a) = some (f b))
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  have arbitrary : ∀ k, ∃ t a, k ≤ t ∧ run0 p t ⟨0,[],[]⟩ = some (f a) := by
    intro k
    induction k with
    | zero => exact ⟨e,a,by omega,first⟩
    | succ k ih =>
      obtain ⟨t,a,ht,hr⟩ := ih
      obtain ⟨s,b,hs,hb⟩ := returns a
      exact ⟨t+s,b,by omega,join0 hr hb⟩
  intro n
  obtain ⟨t,a,ht,hr⟩ := arbitrary n
  have hz : (Agent50Zipper.zrun p t BB6Coverage.Agent31Pump.start).map project = some (f a) :=
    (run_project p t BB6Coverage.Agent31Pump.start).trans hr
  cases h : Agent50Zipper.zrun p t BB6Coverage.Agent31Pump.start with
  | none => simp [h] at hz
  | some z =>
    have H := Agent50Zipper.zrun_sound p m hm t BB6Coverage.Agent31Pump.start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_returns table family [true] 33 entry progress m hm
#print axioms never_of_returns
#print axioms never
end BB6.Agent47Raw41.LB0LC3
