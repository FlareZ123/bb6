module

public import BusyBeaver.BB6.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC
public import CLine
public import CReachBridge

@[expose] public section

namespace BB6.CSourceBridge

open BusyBeaver

namespace Source
export BusyBeaver.M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC
  (State start next encode target is_valid_acceleration)
end Source

abbrev S := Nat × Nat × Nat

def lift : S → Source.State
  | (a,k,c) => .B a k c

theorem start_lift : lift (5,0,1) = Source.start := rfl

/-- The standalone counter-map cases exactly match upstream Cryptids. -/
theorem next_lift (s : S) :
    Source.next (lift s) = Option.map lift (BB6CLine.nextC s) := by
  rcases s with ⟨a,k,c⟩
  rcases c with _ | _ | _ | _ | d
  · rcases a with _ | _ | a
    · rfl
    · rcases k with _ | k <;> rfl
    · rfl
  · rfl
  · rfl
  · rfl
  · rcases a with _ | a <;> rfl

def encodeC (s : S) : Cfg (Fin 2) (Fin 6) := Source.encode (lift s)

/-- The copied Machine C map satisfies the original-TM acceleration contract. -/
theorem is_valid_C : IsValidAcceleration Source.target (5,0,1) encodeC BB6CLine.nextC := by
  have hv := Source.is_valid_acceleration
  refine {
    init_reaches := ?_
    step_some := ?_
    step_none := ?_
  }
  · simpa only [encodeC, start_lift] using hv.init_reaches
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

/-- Raw halting is exactly halting in the locally checked accelerated map. -/
theorem raw_halts_iff_local :
    IsHalt Source.target ↔ CollatzHalts BB6CLine.nextC (5,0,1) :=
  is_valid_C.isHalt_iff

/-- Independently checked finite step semantics matches the upstream convention. -/
theorem iterate_eq_runN (n : Nat) (s : Option S) :
    ((Option.bind · BB6CLine.nextC)^[n] s) = CReachBridge.runN n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change ((Option.bind · BB6CLine.nextC)^[n] (CReachBridge.stepC s)) =
        CReachBridge.runN (n+1) s
      rw [ih (CReachBridge.stepC s)]
      exact (CReachBridge.runN_succ_head n s).symm

theorem collatz_iff_runHalts :
    CollatzHalts BB6CLine.nextC (5,0,1) ↔ CReachBridge.RunHalts := by
  unfold CollatzHalts CReachBridge.RunHalts
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rwa [iterate_eq_runN] at hn
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rwa [iterate_eq_runN]

/-- Verified raw blank-tape halting is equivalent to the exact local stopping guard. -/
theorem raw_halts_iff_reachable_stop :
    IsHalt Source.target ↔
      ∃ s, BB6CLine.Reach s ∧ BB6CLine.nextC s = none :=
  raw_halts_iff_local.trans
    (collatz_iff_runHalts.trans CReachBridge.runHalts_iff_reachable_stop)

/-- Full end-to-end machine-level equivalence for the global diagonal halting gateway. -/
theorem raw_halts_iff_thin :
    IsHalt Source.target ↔ ∃ j : Nat, BB6CLine.Reach (0,2*j,4*j+10) :=
  raw_halts_iff_reachable_stop.trans BB6CLine.stops_iff_thin

#print axioms next_lift
#print axioms is_valid_C
#print axioms raw_halts_iff_thin

end BB6.CSourceBridge
