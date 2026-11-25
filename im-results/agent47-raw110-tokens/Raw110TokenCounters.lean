import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw110TokenCounters
open BB6Coverage

/-- Seven variants of the same E0-hole cylinder. -/
inductive Variant where
  | m42 | m43 | m45 | m47 | m51 | m52 | m55

def a1 : Variant → Move
  | .m42 => ⟨false,false,1⟩
  | .m43 => ⟨false,false,2⟩
  | .m45 => ⟨false,false,5⟩
  | .m47 => ⟨false,true,1⟩
  | .m51 => ⟨true,false,3⟩
  | .m52 => ⟨true,false,4⟩
  | .m55 => ⟨true,true,1⟩

def table (v : Variant) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some (a1 v))
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,2⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

abbrev p4 : List Bool := [false,false,true,true]
abbrev t3 : List Bool := [true,true,true]
abbrev l4 : List Bool := [true,true,false,true]

/-- A common regular language of stable four-cell tokens and three-cell
    tokens. Its grammar is preserved by the full return, not just by sampled
    trajectories. -/
inductive Good : List Bool → Prop
  | nil : Good []
  | four {W : List Bool} : Good W → Good (p4 ++ W)
  | b010 {W : List Bool} : Good W → Good ([false,true,false] ++ W)
  | b011 {W : List Bool} : Good W → Good ([false,true,true] ++ W)
  | b100 {W : List Bool} : Good W → Good ([true,false,false] ++ W)
  | b110 {W : List Bool} : Good W → Good ([true,true,false] ++ W)
  | b111 {W : List Bool} : Good W → Good (t3 ++ W)
  | b000 {W : List Bool} : Good W → Good ([false,false,false] ++ W)

def atB (L W : List Bool) : Z0 := ⟨1,W.headD false::L,W.tail⟩
def atF (L W : List Bool) : Z0 := ⟨5,L,W⟩

def Returns (v : Variant) (L W : List Bool) : Prop :=
  ∃ k U, 0 < k ∧ Good U ∧ run0 (table v) k (atB L W) = some (atF L U)

theorem right4 (v : Variant) (L W : List Bool) : run0 (table v) 6 (atB L (p4++W)) = some (atB (l4++L) W) := by rfl
theorem right010 (v : Variant) (L W : List Bool) : run0 (table v) 3 (atB L ([false,true,false]++W)) = some (atB (t3++L) W) := by rfl
theorem left4 (v : Variant) (L U : List Bool) : run0 (table v) 4 (atF (l4++L) U) = some (atF L (p4++U)) := by rfl
theorem left3 (v : Variant) (L U : List Bool) : run0 (table v) 3 (atF (t3++L) U) = some (atF L (t3++U)) := by rfl
theorem turn110 (v : Variant) (L W : List Bool) : run0 (table v) 1 (atB L ([true,true,false]++W)) = some (atF L ([false,true,false]++W)) := by rfl
theorem turn111 (v : Variant) (L W : List Bool) : run0 (table v) 1 (atB L (t3++W)) = some (atF L ([false,true,true]++W)) := by rfl
theorem turn100 (v : Variant) (L W : List Bool) : run0 (table v) 1 (atB L ([true,false,false]++W)) = some (atF L ([false,false,false]++W)) := by rfl
theorem turn000 (v : Variant) (L W : List Bool) : run0 (table v) 11 (atB L ([false,false,false]++W)) = some (atF L ([true,true,false]++W)) := by rfl
theorem turnNil (v : Variant) (L : List Bool) : run0 (table v) 11 (atB L []) = some (atF L [true,true,false]) := by rfl

theorem turn42 (L W : List Bool) : run0 (table .m42) 5 (atB L ([false,true,true]++W)) = some (atF L ([true,false,false]++W)) := by rfl
theorem turn45 (L W : List Bool) : run0 (table .m45) 5 (atB L ([false,true,true]++W)) = some (atF L ([true,true,false]++W)) := by rfl
theorem turn52 (L W : List Bool) : run0 (table .m52) 9 (atB L ([false,true,true]++W)) = some (atF L ([true,true,false]++W)) := by rfl
theorem right43 (L W : List Bool) : run0 (table .m43) 5 (atB L ([false,true,true]++W)) = some (atB (t3++L) W) := by rfl
theorem right51 (L W : List Bool) : run0 (table .m51) 7 (atB L ([false,true,true]++W)) = some (atB (t3++L) W) := by rfl
theorem right55 (L W : List Bool) : run0 (table .m55) 3 (atB L ([false,true,true]++W)) = some (atB (t3++L) W) := by rfl
theorem right47 (L W : List Bool) : run0 (table .m47) 3 (atB L ([false,true,true]++W)) = some (atB ([false,true,true]++L) W) := by rfl
theorem left47 (L U : List Bool) : run0 (table .m47) 3 (atF ([false,true,true]++L) U) = some (atF L ([true,false,false]++U)) := by rfl

theorem scan (v : Variant) {W : List Bool} (h : Good W) (L : List Bool) : Returns v L W := by
  induction h generalizing L with
  | nil => exact ⟨11,_,by decide,Good.b110 Good.nil,turnNil v L⟩
  | four h ih =>
    obtain ⟨k,U,hk,hu,hr⟩ := ih (l4++L)
    exact ⟨6+k+4,_,by omega,Good.four hu,join0 (join0 (right4 v L _) hr) (left4 v L U)⟩
  | b010 h ih =>
    obtain ⟨k,U,hk,hu,hr⟩ := ih (t3++L)
    exact ⟨3+k+3,_,by omega,Good.b111 hu,join0 (join0 (right010 v L _) hr) (left3 v L U)⟩
  | b011 h ih =>
    cases v with
    | m42 => exact ⟨5,_,by decide,Good.b100 h,turn42 L _⟩
    | m43 =>
      obtain ⟨k,U,hk,hu,hr⟩ := ih (t3++L)
      exact ⟨5+k+3,_,by omega,Good.b111 hu,join0 (join0 (right43 L _) hr) (left3 .m43 L U)⟩
    | m45 => exact ⟨5,_,by decide,Good.b110 h,turn45 L _⟩
    | m47 =>
      obtain ⟨k,U,hk,hu,hr⟩ := ih ([false,true,true]++L)
      exact ⟨3+k+3,_,by omega,Good.b100 hu,join0 (join0 (right47 L _) hr) (left47 L U)⟩
    | m51 =>
      obtain ⟨k,U,hk,hu,hr⟩ := ih (t3++L)
      exact ⟨7+k+3,_,by omega,Good.b111 hu,join0 (join0 (right51 L _) hr) (left3 .m51 L U)⟩
    | m52 => exact ⟨9,_,by decide,Good.b110 h,turn52 L _⟩
    | m55 =>
      obtain ⟨k,U,hk,hu,hr⟩ := ih (t3++L)
      exact ⟨3+k+3,_,by omega,Good.b111 hu,join0 (join0 (right55 L _) hr) (left3 .m55 L U)⟩
  | b100 h ih => exact ⟨1,_,by decide,Good.b000 h,turn100 v L _⟩
  | b110 h ih => exact ⟨1,_,by decide,Good.b010 h,turn110 v L _⟩
  | b111 h ih => exact ⟨1,_,by decide,Good.b011 h,turn111 v L _⟩
  | b000 h ih => exact ⟨11,_,by decide,Good.b110 h,turn000 v L _⟩

def baseConf (W : List Bool) : Z0 := ⟨1,[],[false,true,true]++W⟩
theorem start (v : Variant) (W : List Bool) : run0 (table v) 6 (baseConf W) = some (atB l4 W) := by rfl
theorem finish (v : Variant) (U : List Bool) : run0 (table v) 17 (atF l4 U) = some (baseConf (p4++U)) := by rfl

def BaseReturns (v : Variant) (W : List Bool) : Prop := ∃ k U, 0 < k ∧ Good U ∧ run0 (table v) k (baseConf W) = some (baseConf U)
theorem baseReturns (v : Variant) (W : List Bool) (h : Good W) : BaseReturns v W := by
  obtain ⟨k,U,hk,hu,hr⟩ := scan v h l4
  exact ⟨6+k+17,_,by omega,Good.four hu,join0 (join0 (start v W) hr) (finish v U)⟩

noncomputable def next (v : Variant) (s : {W : List Bool // Good W}) : {W : List Bool // Good W} :=
  ⟨Classical.choose (Classical.choose_spec (baseReturns v s.val s.property)), (Classical.choose_spec (Classical.choose_spec (baseReturns v s.val s.property))).2.1⟩
noncomputable def cost (v : Variant) (s : {W : List Bool // Good W}) : Nat := Classical.choose (baseReturns v s.val s.property)
theorem cost_pos (v : Variant) (s : {W : List Bool // Good W}) : 0 < cost v s := (Classical.choose_spec (Classical.choose_spec (baseReturns v s.val s.property))).1
theorem ret (v : Variant) (s : {W : List Bool // Good W}) : run0 (table v) (cost v s) (baseConf s.val) = some (baseConf (next v s).val) := (Classical.choose_spec (Classical.choose_spec (baseReturns v s.val s.property))).2.2

noncomputable def words (v : Variant) : Nat → {W : List Bool // Good W}
  | 0 => ⟨p4++p4++p4++[false,true,false],Good.four (Good.four (Good.four (Good.b010 Good.nil)))⟩
  | n+1 => next v (words v n)
theorem entry (v : Variant) : run0 (table v) 126 ⟨0,[],[]⟩ = some (baseConf (words v 0).val) := by cases v <;> rfl

theorem never (v : Variant) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) (fun n => baseConf (words v n).val) 126 (fun n => cost v (words v n)) (entry v)
    (fun n => cost_pos v (words v n)) (fun n => ret v (words v n)) m hm
#print axioms never

namespace M42
abbrev table := Raw110TokenCounters.table .m42
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Raw110TokenCounters.never .m42 m hm
#print axioms never
end M42

namespace M43
abbrev table := Raw110TokenCounters.table .m43
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Raw110TokenCounters.never .m43 m hm
#print axioms never
end M43

namespace M45
abbrev table := Raw110TokenCounters.table .m45
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Raw110TokenCounters.never .m45 m hm
#print axioms never
end M45

namespace M47
abbrev table := Raw110TokenCounters.table .m47
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Raw110TokenCounters.never .m47 m hm
#print axioms never
end M47

namespace M51
abbrev table := Raw110TokenCounters.table .m51
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Raw110TokenCounters.never .m51 m hm
#print axioms never
end M51

namespace M52
abbrev table := Raw110TokenCounters.table .m52
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Raw110TokenCounters.never .m52 m hm
#print axioms never
end M52

namespace M55
abbrev table := Raw110TokenCounters.table .m55
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Raw110TokenCounters.never .m55 m hm
#print axioms never
end M55
end BB6Coverage.Agent31Pump.Raw110TokenCounters
