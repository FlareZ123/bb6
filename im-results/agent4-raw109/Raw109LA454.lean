import SweepPumping
import Raw58Live

namespace BB6Coverage.Agent4Raw109LA454
open Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨true,true,1⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

inductive Right : List Bool → Prop where
  | nil : Right []
  | zero (R : List Bool) : Right R → Right (false::false::R)
  | one (R : List Bool) : Right R → Right (false::true::R)

inductive Left : List Bool → Prop where
  | nil : Left []
  | short (L : List Bool) : Left L → Left (true::true::L)
  | long (L : List Bool) : Left L → Left (true::true::true::false::L)

def F (L R : List Bool) : Z0 := ⟨5,L,R⟩
def D (L R : List Bool) : Z0 := ⟨3,true::false::L,R⟩

theorem go (R : List Bool) :
    run0 table 2 (F [] R) = some (D [] R) := by rfl
theorem scanShort (L R : List Bool) :
    run0 table 10 (D L (false::true::R)) =
      some (D (true::true::L) R) := by rfl
theorem scanLong (L R : List Bool) :
    run0 table 6 (D L (false::false::false::true::R)) =
      some (D (true::true::true::false::L) R) := by rfl
theorem scanEnd (L R : List Bool) :
    run0 table 12 (D L (false::false::false::false::R)) =
      some (F (true::true::true::false::L) (false::true::R)) := by rfl
theorem scanNil (L : List Bool) :
    run0 table 12 (D L []) =
      some (F (true::true::true::false::L) [false,true]) := by rfl
theorem scanZero (L : List Bool) :
    run0 table 12 (D L [false,false]) =
      some (F (true::true::true::false::L) [false,true]) := by rfl

theorem scan (R : List Bool) (hR : Right R) (L : List Bool) (hL : Left L) :
    ∃ t M W, 0<t ∧ run0 table t (D L R) = some (F M W) ∧ Left M ∧ Right W := by
  cases hR with
  | nil => exact ⟨12,_,_,by omega,scanNil L,Left.long L hL,Right.one [] Right.nil⟩
  | one R hR =>
    obtain ⟨t,M,W,ht,hr,hm,hw⟩ := scan R hR (true::true::L) (Left.short L hL)
    exact ⟨10+t,M,W,by omega,join0 (scanShort L R) hr,hm,hw⟩
  | zero R hR =>
    cases hR with
    | nil => exact ⟨12,_,_,by omega,scanZero L,Left.long L hL,Right.one [] Right.nil⟩
    | zero R hR =>
      exact ⟨12,_,_,by omega,scanEnd L R,Left.long L hL,Right.one R hR⟩
    | one R hR =>
      obtain ⟨t,M,W,ht,hr,hm,hw⟩ := scan R hR (true::true::true::false::L) (Left.long L hL)
      exact ⟨6+t,M,W,by omega,join0 (scanLong L R) hr,hm,hw⟩
termination_by R.length
decreasing_by all_goals simp_wf; omega

theorem returnShort (L R : List Bool) :
    run0 table 2 (F (true::true::L) R) =
      some (F L (false::false::R)) := by rfl
theorem returnLong (L R : List Bool) :
    run0 table 14 (F (true::true::true::false::L) R) =
      some (F L (false::false::false::true::R)) := by rfl

theorem retreat (L : List Bool) (hL : Left L) (R : List Bool) (hR : Right R) :
    ∃ t W, run0 table t (F L R) = some (F [] W) ∧ Right W := by
  induction hL generalizing R with
  | nil => exact ⟨0,R,rfl,hR⟩
  | short L hL ih =>
    obtain ⟨t,W,hr,hw⟩ := ih (false::false::R) (Right.zero R hR)
    exact ⟨2+t,W,join0 (returnShort L R) hr,hw⟩
  | long L hL ih =>
    obtain ⟨t,W,hr,hw⟩ := ih (false::false::false::true::R) (Right.zero _ (Right.one R hR))
    exact ⟨14+t,W,join0 (returnLong L R) hr,hw⟩

theorem progress (R : List Bool) (hR : Right R) :
    ∃ t W, 0<t ∧ run0 table t (F [] R) = some (F [] W) ∧ Right W := by
  obtain ⟨t,M,W,ht,hr,hm,hw⟩ := scan R hR [] Left.nil
  obtain ⟨u,V,hs,hv⟩ := retreat M hm W hw
  exact ⟨2+t+u,V,by omega,join0 (join0 (go R) hr) hs,hv⟩

theorem entry : run0 table 11 ⟨0,[],[]⟩ = some (F [] [false,false,false,true]) := by rfl
theorem arbitrary (n : Nat) :
    ∃ t ≥ n, ∃ z, run0 table t ⟨0,[],[]⟩ = some z := by
  have h : ∀ k : Nat, ∃ t ≥ k, ∃ R, Right R ∧ run0 table t ⟨0,[],[]⟩ = some (F [] R) := by
    intro k
    induction k with
    | zero => exact ⟨11,by omega,_,Right.zero _ (Right.one [] Right.nil),entry⟩
    | succ k ih =>
      obtain ⟨t,ht,R,hr,hs⟩ := ih
      obtain ⟨u,W,hu,hw,hW⟩ := progress R hr
      exact ⟨t+u,W,by omega,hW,join0 hs hw⟩
  obtain ⟨t,ht,R,_,hr⟩ := h n
  exact ⟨t,ht,F [] R,hr⟩
#print axioms arbitrary

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table (fun n => by
    obtain ⟨t,ht,z,hr⟩ := arbitrary n
    exact ⟨t,z,ht,hr⟩) m hm
#print axioms never
end BB6Coverage.Agent4Raw109LA454
