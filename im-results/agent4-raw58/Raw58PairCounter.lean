import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent4PairCounter
open BB6Coverage Agent31Pump Agent50Zipper

def A (R : List Bool) : Z0 := ⟨0,[true,false,true,true],R⟩
def C (k : Nat) (R : List Bool) : Z0 :=
  ⟨2,R.headD false :: false :: false :: (rep [false,false] k ++ [true,true]),R.tail⟩
def D (lp : List Bool) (k : Nat) (R : List Bool) : Z0 :=
  ⟨3,lp ++ rep [false,false] k ++ [true,true],R⟩

inductive Code : List Bool → Prop
  | nil : Code []
  | pair (b : Bool) (r : List Bool) : Code r → Code (true::b::r)

theorem pairPrefix (k : Nat) (r : List Bool) (h : Code r) :
    Code (rep [true,true] k ++ r) := by
  induction k with
  | zero => exact h
  | succ k ih => exact Code.pair true _ ih

theorem ones_comm (k : Nat) (r : List Bool) :
    true :: (rep [true,true] k ++ r) = rep [true,true] k ++ true::r := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [rep,List.cons_append,List.nil_append,List.cons.injEq,true_and] using ih

theorem clear (p : PartialMachine) (lp : List Bool)
    (one : ∀ L R, run0 p 2 ⟨3,lp++[false,false]++L,[]++R⟩ =
      some ⟨3,lp++L,[]++[true,true]++R⟩)
    (k : Nat) (R : List Bool) :
    run0 p (2*k) (D lp k R) = some (D lp 0 (rep [true,true] k ++ R)) := by
  simpa only [D,rep,List.nil_append,List.append_nil] using
    (sweepL p 3 lp [] [false,false] [true,true] 2 one k [true,true] R)

/-- Binary countdown on finite pairs 1b. Carried pairs become zeros and the
reset changes them to pairs 11. No numerical runtime bound is assumed. -/
theorem returns (p : PartialMachine) (ca cs ce : Nat)
    (carry : ∀ k r, run0 p ca (C k (true::false::r)) = some (C (k+1) r))
    (stop : ∀ k r, run0 p (cs+2*k) (C k (true::true::r)) =
        some (A (rep [true,true] k ++ true::false::r)))
    (empty : ∀ k, run0 p (ce+2*k) (C k []) = some (A (rep [true,true] (k+1))))
    (hcs : 0 < cs) (hce : 0 < ce)
    (k : Nat) (r : List Bool) (hr : Code r) :
    ∃ t s, 0 < t ∧ Code s ∧ run0 p t (C k r) = some (A s) := by
  induction hr generalizing k with
  | nil => exact ⟨ce+2*k,rep [true,true] (k+1),by omega,by simpa only [List.append_nil] using pairPrefix (k+1) [] Code.nil,empty k⟩
  | pair b r h ih =>
    cases b with
    | false =>
      obtain ⟨t,s,ht,hs,hret⟩ := ih (k+1)
      exact ⟨ca+t,s,by omega,hs,join0 (carry k r) hret⟩
    | true => exact ⟨cs+2*k,_,by omega,pairPrefix k _ (Code.pair false r h),stop k r⟩

theorem arbitrary (p : PartialMachine) (en ac ca cs ce : Nat)
    (entry : run0 p en ⟨0,[],[]⟩ = some (A []))
    (anchor : ∀ r, run0 p ac (A r) = some (C 0 r))
    (carry : ∀ k r, run0 p ca (C k (true::false::r)) = some (C (k+1) r))
    (stop : ∀ k r, run0 p (cs+2*k) (C k (true::true::r)) =
        some (A (rep [true,true] k ++ true::false::r)))
    (empty : ∀ k, run0 p (ce+2*k) (C k []) = some (A (rep [true,true] (k+1))))
    (hcs : 0 < cs) (hce : 0 < ce) (n : Nat) :
    ∃ t r, n ≤ t ∧ Code r ∧ run0 p t ⟨0,[],[]⟩ = some (A r) := by
  induction n with
  | zero => exact ⟨en,[],by omega,Code.nil,entry⟩
  | succ n ih =>
    obtain ⟨t,r,ht,hr,hh⟩ := ih
    obtain ⟨u,s,hu,hs,hret⟩ := returns p ca cs ce carry stop empty hcs hce 0 r hr
    exact ⟨t+(ac+u),s,by omega,hs,join0 hh (join0 (anchor r) hret)⟩

theorem never (p : PartialMachine) (en ac ca cs ce : Nat)
    (entry : run0 p en ⟨0,[],[]⟩ = some (A []))
    (anchor : ∀ r, run0 p ac (A r) = some (C 0 r))
    (carry : ∀ k r, run0 p ca (C k (true::false::r)) = some (C (k+1) r))
    (stop : ∀ k r, run0 p (cs+2*k) (C k (true::true::r)) =
        some (A (rep [true,true] k ++ true::false::r)))
    (empty : ∀ k, run0 p (ce+2*k) (C k []) = some (A (rep [true,true] (k+1))))
    (hcs : 0 < cs) (hce : 0 < ce)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  intro n
  obtain ⟨t,r,ht,_,hr⟩ := arbitrary p en ac ca cs ce entry anchor carry stop empty hcs hce n
  have hz : (zrun p t Agent31Pump.start).map project = some (A r) :=
    (run_project p t Agent31Pump.start).trans hr
  cases h : zrun p t Agent31Pump.start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound p m hm t Agent31Pump.start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms arbitrary
#print axioms never
end BB6Coverage.Agent4PairCounter
