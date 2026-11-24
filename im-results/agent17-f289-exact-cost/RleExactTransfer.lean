import RleCountedAll
import BusyBeaver.Bridge

open BusyBeaver
namespace BB6.Agent17.RleCounted

/-- Convert an exact successful-step certificate to primitive halting score,
without a simulation of the enormous raw tape. -/
theorem canHaltAt_run_score {M : Machine (Fin 2) (Fin 6)} {n : Nat}
    (h : CanHaltAt M (init []) n) :
    (multiStep M (init []) n).isSome = true ∧
      multiStep M (init []) (n+1) = none := by
  obtain ⟨c, hc, hstop⟩ := h
  change multiStep M (init []) n = some c at hc
  constructor
  · rw [hc]; rfl
  · rw [multiStep_succ', hc]
    exact Option.isNone_iff_eq_none.mp hstop

/-- Exact time transfer through the upstream library's canonical embedding. -/
theorem canHaltAt_conjecture_score
    {M : ConjectureMachines.Machine 6 2} {n : Nat}
    (h : CanHaltAt M.toBB (init []) n) :
    (((fun y : Option (ConjectureMachines.Cfg 6 2) =>
        y.bind (ConjectureMachines.step M))^[n]
          (some ConjectureMachines.init)).isSome = true) ∧
    (fun y : Option (ConjectureMachines.Cfg 6 2) =>
        y.bind (ConjectureMachines.step M))^[n+1]
          (some ConjectureMachines.init) = none := by
  obtain ⟨h₁, h₂⟩ := canHaltAt_run_score h
  rw [ConjectureMachines.init_toBB, ConjectureMachines.multiStep_toBB,
    Option.isSome_map] at h₁
  rw [ConjectureMachines.init_toBB, ConjectureMachines.multiStep_toBB,
    Option.map_eq_none_iff] at h₂
  exact ⟨h₁, h₂⟩

theorem first_source_score :
    let M := BusyBeaver.M_1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LAHHH.machine
    let n := 932242535661307148726923126800831715518673957228
    (((fun y : Option (ConjectureMachines.Cfg 6 2) =>
        y.bind (ConjectureMachines.step M))^[n]
          (some ConjectureMachines.init)).isSome = true) ∧
    (fun y : Option (ConjectureMachines.Cfg 6 2) =>
        y.bind (ConjectureMachines.step M))^[n+1]
          (some ConjectureMachines.init) = none :=
  canHaltAt_conjecture_score First.halts_exact

theorem second_source_score :
    let M := BusyBeaver.M_1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RDHHH.machine
    let n := 111579188581812927653348117002306046024821208051411619955580898884568781
    (((fun y : Option (ConjectureMachines.Cfg 6 2) =>
        y.bind (ConjectureMachines.step M))^[n]
          (some ConjectureMachines.init)).isSome = true) ∧
    (fun y : Option (ConjectureMachines.Cfg 6 2) =>
        y.bind (ConjectureMachines.step M))^[n+1]
          (some ConjectureMachines.init) = none :=
  canHaltAt_conjecture_score Second.halts_exact

#print axioms first_source_score
#print axioms second_source_score

end BB6.Agent17.RleCounted
