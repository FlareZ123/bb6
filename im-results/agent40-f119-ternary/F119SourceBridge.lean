import BusyBeaver.BB6.M_1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_HHH1LB
import F119RootInverse2

namespace F119SourceBridge
open BusyBeaver
namespace Source
export BusyBeaver.M_1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_HHH1LB
  (State start next encode target is_valid_acceleration)
end Source

def lift : F119.State → Source.State
  | .D a b c => .D a b c

def encodeLocal (s : F119.State) : Cfg (Fin 2) (Fin 6) :=
  Source.encode (lift s)

theorem next_lift (s : F119.State) :
    Source.next (lift s) = Option.map lift (F119.next s) := by
  rcases s with ⟨a,b,c⟩
  rcases b with _ | _ | _ | b
  · rcases c with _ | _ | _ | c <;> rfl
  · rcases c with _ | c <;> rfl
  · rfl
  · rcases c with _ | c <;>
      by_cases h0 : b % 3 = 0 <;> by_cases h1 : b % 3 = 1 <;>
      simp [Source.next, F119.next, lift, h0, h1]

theorem valid_local :
    IsValidAcceleration Source.target (F119.State.D 0 3 1)
      encodeLocal F119.next := by
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

def iterate : Nat → Option F119.State → Option F119.State
  | 0, s => s
  | n+1, s => iterate n (s.bind F119.next)

theorem stops_iter {n : Nat} {s : F119.State} (h : F119.Stops n s) :
    iterate (n+1) (some s) = none := by
  induction h with
  | now h => simpa [iterate] using h
  | later h _ ih => simpa [iterate, h] using ih

theorem iter_stops (n : Nat) (s : F119.State) (h : iterate n (some s)=none) : F119.Halts s := by
  induction n generalizing s with
  | zero => simp [iterate] at h
  | succ n ih =>
    cases he : F119.next s with
    | none => exact ⟨0, F119.Stops.now he⟩
    | some t =>
      have ht : iterate n (some t)=none := by simpa [iterate, he] using h
      obtain ⟨k,hk⟩ := ih t ht
      exact ⟨k+1, F119.Stops.later he hk⟩

theorem halts_iff (s : F119.State) : F119.Halts s ↔ ∃ n, iterate n (some s)=none := by
  constructor
  · rintro ⟨n,h⟩
    exact ⟨n+1, stops_iter h⟩
  · rintro ⟨n,h⟩
    exact iter_stops n s h

theorem iter_agree (n : Nat) (s : Option F119.State) :
    ((fun x : Option F119.State => x.bind F119.next)^[n] s) = iterate n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih (s.bind F119.next)

theorem raw_halts_iff_local : IsHalt Source.target ↔ F119.Halts (.D 0 3 1) := by
  have hb := valid_local.isHalt_iff
  unfold CollatzHalts at hb
  rw [halts_iff]
  simpa only [iter_agree, Option.isNone_iff_eq_none] using hb

theorem raw_halts_iff_second_classes : IsHalt Source.target ↔
    ∃ k, F119RootInverse2.secondClasses k ∧ F119.MacroReach F119.start (3^k,1) :=
  raw_halts_iff_local.trans F119RootInverse2.root_halts_iff_second_classes

#print axioms next_lift
#print axioms raw_halts_iff_local
#print axioms raw_halts_iff_second_classes
end F119SourceBridge
