module

public import BusyBeaver.BB6.M_1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_HHH1LE
public import SheepBlankCriterion

@[expose] public section

namespace BB6.Agent22.SheepSource

open BusyBeaver
namespace Source
export BusyBeaver.M_1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_HHH1LE
  (State start next encode target is_valid_acceleration isHalt_iff_acceleration)
end Source

/-- Every local pair is literally the corresponding upstream symbolic state. -/
def lift : SheepBridge.State → Source.State
  | (m,k) => .P m k

def encodeLocal (s : SheepBridge.State) : Cfg (Fin 2) (Fin 6) :=
  Source.encode (lift s)

/-- Complete branch-by-branch equality, including the halting branch. -/
theorem next_lift (s : SheepBridge.State) :
    Source.next (lift s) = Option.map lift (SheepBridge.nextA s) := by
  rcases s with ⟨m,k⟩
  rcases m with _ | _ | m
  · rcases k with _ | k <;> rfl
  · rfl
  · by_cases hm : m % 2 = 0 <;> simp [Source.next, SheepBridge.nextA, lift, hm]

/-- Transfer the upstream machine-certified acceleration to the exact
counter rules used by SheepPowerBridge. -/
theorem valid_local :
    IsValidAcceleration Source.target ((0,2) : SheepBridge.State)
      encodeLocal SheepBridge.nextA := by
  have hv := Source.is_valid_acceleration
  refine { init_reaches := ?_, step_some := ?_, step_none := ?_ }
  · simpa only [encodeLocal, Source.start, lift] using hv.init_reaches
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

/-- Abstract local iterates agree exactly with Cryptids' convention. -/
theorem iter_agree (n : Nat) (s : Option SheepBridge.State) :
    Function.iterate (fun x : Option SheepBridge.State => x.bind SheepBridge.nextA) n s =
      BB6.Agent22.iter SheepBridge.nextA n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change Function.iterate (fun x : Option SheepBridge.State => x.bind SheepBridge.nextA) n
      (s.bind SheepBridge.nextA) =
      BB6.Agent22.iter SheepBridge.nextA (n+1) s
    rw [ih]
    have hs := BB6.Agent22.iter_add SheepBridge.nextA 1 n s
    have he : 1+n=n+1 := by omega
    rw [he] at hs
    exact hs.symm

theorem raw_halts_iff_local :
    IsHalt Source.target ↔
      ∃ n, BB6.Agent22.iter SheepBridge.nextA n
        (some ((0,2) : SheepBridge.State)) = none := by
  have hb := valid_local.isHalt_iff
  unfold CollatzHalts at hb
  simpa only [iter_agree, Option.isNone_iff_eq_none] using hb

/-- End-to-end original six-state blank-tape semantic equivalence.
The remaining mathematical problem is whether the t=5 section orbit
reaches any power of two, not whether the reduction is faithful. -/
theorem raw_halts_iff_power :
    IsHalt Source.target ↔
      ∃ a, 2 ≤ a ∧ BB6.Agent22.Sheep.Reach 5 (2^a) :=
  raw_halts_iff_local.trans BB6.Agent22.Sheep.counter_blank_halts_iff_power

#print axioms next_lift
#print axioms valid_local
#print axioms raw_halts_iff_power

end BB6.Agent22.SheepSource
