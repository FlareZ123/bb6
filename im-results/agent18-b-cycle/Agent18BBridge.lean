module

public import BusyBeaver.BB6.M_1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_HHH1RE
public import Agent18BReduction

@[expose] public section

namespace BB6.Bridge

open BusyBeaver
namespace Source
export BusyBeaver.M_1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_HHH1RE
  (State start next encode target is_valid_acceleration)
end Source

/-- Convert the exact local triple to the upstream certified symbolic state. -/
def lift : BReduction.S → Source.State
  | (a,b,c) => .A a b c

theorem start_lift : lift (3,0,0) = Source.start := rfl

/-- Kernel-level semantic equality: every copied branch equals the upstream branch. -/
theorem next_lift (s : BReduction.S) :
    Source.next (lift s) = Option.map lift (BReduction.nextB s) := by
  rcases s with ⟨a,b,c⟩
  rcases b with _ | _ | b
  · rcases a with _ | a <;> rfl
  · rcases a with _ | a <;> rfl
  · have he : b + 1 + 1 = b + 2 := by omega
    rw [he]
    simp [Source.next, BReduction.nextB, lift]

/-- Concrete original-machine configuration assigned to each local triple. -/
def encodeB (s : BReduction.S) : Cfg (Fin 2) (Fin 6) :=
  Source.encode (lift s)

/-- Reuse upstream machine simulation and prove the local map satisfies its exact contract. -/
theorem is_valid_B : IsValidAcceleration Source.target (3,0,0) encodeB BReduction.nextB := by
  have hv := Source.is_valid_acceleration
  refine {
    init_reaches := ?_
    step_some := ?_
    step_none := ?_
  }
  · simpa only [encodeB, start_lift] using hv.init_reaches
  · intro s t hst
    have hs : Source.next (lift s) = some (lift t) := by
      rw [next_lift, hst]
      rfl
    exact hv.step_some (lift s) (lift t) hs
  · intro s hst
    have hs : Source.next (lift s) = none := by
      rw [next_lift, hst]
      rfl
    exact hv.step_none (lift s) hs

/-- Full raw blank-tape halting iff local triple-system halting, kernel-checked against source. -/
theorem raw_halts_iff :
    IsHalt Source.target ↔ CollatzHalts BReduction.nextB (3,0,0) :=
  is_valid_B.isHalt_iff

#print axioms next_lift
#print axioms is_valid_B
#print axioms raw_halts_iff

end BB6.Bridge
