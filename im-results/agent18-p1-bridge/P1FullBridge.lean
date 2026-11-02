import P1Bridge
import BlankCriterion

namespace BB6.P1FullBridge

open BB6.HaltingFunnel
open BB6.P1Bridge
open BusyBeaver

def nextT (s : Nat × Nat) : Option (Nat × Nat) :=
  T s.1 s.2

/-- Finite iteration of the independently defined local high-level P1 accelerator. -/
def runT : Nat → Option (Nat × Nat) → Option (Nat × Nat)
  | 0,s => s
  | n+1,s => runT n (s.bind nextT)

/-- Every exact local halting trace supplies a finite failed iteration. -/
theorem local_to_run (n a c : Nat) (hh : HaltsIn n a c) :
    (runT n (some (a,c))).isNone := by
  induction hh with
  | now a c h =>
      simp [runT, nextT, h]
  | next m a c b d h hh ih =>
      change (runT m (nextT (a,c))).isNone
      rw [show nextT (a,c) = some (b,d) by exact h]
      exact ih

/-- Every finite failed iteration admits an exact local halting certificate. -/
theorem run_to_local (n a c : Nat) (hh : (runT n (some (a,c))).isNone) :
    ∃ m : Nat, HaltsIn m a c := by
  induction n generalizing a c with
  | zero => simp [runT] at hh
  | succ n ih =>
      change (runT n (nextT (a,c))).isNone at hh
      cases hnext : T a c with
      | none => exact ⟨1, HaltsIn.now a c hnext⟩
      | some bd =>
          rcases bd with ⟨b,d⟩
          have hT : nextT (a,c) = some (b,d) := by simpa [nextT] using hnext
          rw [hT] at hh
          obtain ⟨m,hm⟩ := ih b d hh
          exact ⟨m+1, HaltsIn.next m a c b d hnext hm⟩

theorem local_iff_run :
    (∃ n : Nat, HaltsIn n 2 1) ↔
    (∃ n : Nat, (runT n (some (2,1))).isNone) := by
  constructor
  · rintro ⟨n,hn⟩
    exact ⟨n,local_to_run n 2 1 hn⟩
  · rintro ⟨n,hn⟩
    exact run_to_local n 2 1 hn

/-- Match standard Function.iterate to the local primitive-recursive finite-step definition. -/
theorem iterate_eq_run (n : Nat) (s : Option (Nat × Nat)) :
    ((Option.bind · nextT)^[n] s) = runT n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih (s.bind nextT)

/-- The original machine's formally certified acceleration commutes with our map. -/
theorem map_compat (s : Option (Nat × Nat)) :
    (Option.map liftPair s).bind Source.highLevelNext =
      Option.map liftPair (s.bind nextT) := by
  cases s with
  | none => rfl
  | some t =>
      rcases t with ⟨a,c⟩
      simpa [nextT] using T_eq_highLevelNext a c

theorem iterate_lift (n : Nat) (s : Option (Nat × Nat)) :
    ((Option.bind · Source.highLevelNext)^[n] (Option.map liftPair s)) =
      Option.map liftPair (((Option.bind · nextT)^[n] s)) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      rw [map_compat]
      exact ih (s.bind nextT)

theorem isNone_equiv (n : Nat) :
    (((Option.bind · Source.highLevelNext)^[n] (some Source.highLevelStart)).isNone) =
      (runT n (some (2,1))).isNone := by
  change (((Option.bind · Source.highLevelNext)^[n]
      (Option.map liftPair (some (2,1)))).isNone) = _
  rw [iterate_lift, iterate_eq_run]
  cases runT n (some (2,1)) <;> rfl

theorem collatz_iff_run :
    CollatzHalts Source.highLevelNext Source.highLevelStart ↔
    (∃ n : Nat, (runT n (some (2,1))).isNone) := by
  unfold CollatzHalts
  constructor
  · rintro ⟨n,hn⟩
    exact ⟨n,by rwa [isNone_equiv n] at hn⟩
  · rintro ⟨n,hn⟩
    exact ⟨n,by rwa [← isNone_equiv n] at hn⟩

/-- Semantics connection from the six-state, two-symbol blank tape to
    the independently established local P1 formal halting relation. -/
theorem raw_iff_local :
    IsHalt Source.target ↔ ∃ n : Nat, HaltsIn n 2 1 :=
  Source.isHalt_iff_highLevel_acceleration.trans
    (collatz_iff_run.trans local_iff_run.symm)

/-- Exact raw-machine blank-tape halting iff the sparse exponential critical
    family is reached. The arithmetic target result is from Agent 4. -/
theorem raw_halts_iff_sparse :
    IsHalt Source.target ↔
    (∃ n : Nat, ReachT 2 1 2 (14*2^n-2*n-10)) :=
  raw_iff_local.trans blank_halts_iff_closed

#print axioms raw_halts_iff_sparse
#print axioms raw_iff_local
end BB6.P1FullBridge
