import RleCountedAll
import CryptidsHaltIff

namespace BB6.Agent17.F289Coverage
open BB6Coverage BB6.ConjectureBridge BB6.Agent17.RleCounted

theorem sourceRun_eq_iterate (m : ConjectureMachines.Machine 6 2) (n : Nat) :
    sourceRun m n =
      (fun y : Option (ConjectureMachines.Cfg 6 2) =>
        y.bind (ConjectureMachines.step m))^[n] (some ConjectureMachines.init) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sourceRun, Function.iterate_succ_apply', ← ih]

theorem counted_to_local_score (m : ConjectureMachines.Machine 6 2) (n : Nat)
    (h : CanHaltAt m.toBB (BusyBeaver.init []) n) :
    HaltsAfter (toAgent8 m) n := by
  apply (source_halts_after_iff_agent8_halts_after m n).mp
  rw [sourceRun_eq_iterate, sourceRun_eq_iterate]
  exact canHaltAt_conjecture_score h

def source_1 : ConjectureMachines.Machine 6 2 :=
  BusyBeaver.M_1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LAHHH.machine

def expectedRLE_1 : Machine := fun slot =>
  match slot.1.val, slot.2 with
  | 0, false => some ⟨true, true, 1⟩
  | 0, true => some ⟨false, true, 4⟩
  | 1, false => some ⟨true, true, 2⟩
  | 1, true => some ⟨false, true, 0⟩
  | 2, false => some ⟨false, false, 3⟩
  | 2, true => some ⟨false, false, 1⟩
  | 3, false => some ⟨false, false, 0⟩
  | 3, true => some ⟨true, false, 4⟩
  | 4, false => some ⟨true, false, 2⟩
  | 4, true => some ⟨true, false, 5⟩
  | 5, false => some ⟨false, false, 0⟩
  | 5, true => none
  | _, _ => none

theorem source_eq_literal_1 :
    toAgent8 source_1 = expectedRLE_1 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl

theorem literal_score_1 : HaltsAfter expectedRLE_1 932242535661307148726923126800831715518673957228 := by
  rw [← source_eq_literal_1]
  exact counted_to_local_score source_1 _ First.halts_exact

#print axioms literal_score_1

def source_2 : ConjectureMachines.Machine 6 2 :=
  BusyBeaver.M_1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RDHHH.machine

def expectedRLE_2 : Machine := fun slot =>
  match slot.1.val, slot.2 with
  | 0, false => some ⟨true, true, 1⟩
  | 0, true => some ⟨true, true, 5⟩
  | 1, false => some ⟨false, true, 2⟩
  | 1, true => some ⟨false, true, 4⟩
  | 2, false => some ⟨false, true, 3⟩
  | 2, true => some ⟨true, true, 0⟩
  | 3, false => some ⟨true, false, 4⟩
  | 3, true => some ⟨false, false, 0⟩
  | 4, false => some ⟨true, false, 1⟩
  | 4, true => some ⟨false, false, 3⟩
  | 5, false => some ⟨false, true, 3⟩
  | 5, true => none
  | _, _ => none

theorem source_eq_literal_2 :
    toAgent8 source_2 = expectedRLE_2 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl

theorem literal_score_2 : HaltsAfter expectedRLE_2 111579188581812927653348117002306046024821208051411619955580898884568781 := by
  rw [← source_eq_literal_2]
  exact counted_to_local_score source_2 _ Second.halts_exact

#print axioms literal_score_2

theorem first_score_attainable : Attainable 932242535661307148726923126800831715518673957229 :=
  ⟨expectedRLE_1, 932242535661307148726923126800831715518673957228, literal_score_1, rfl⟩

theorem second_score_attainable : Attainable 111579188581812927653348117002306046024821208051411619955580898884568782 :=
  ⟨expectedRLE_2, 111579188581812927653348117002306046024821208051411619955580898884568781, literal_score_2, rfl⟩

#print axioms first_score_attainable
#print axioms second_score_attainable

end BB6.Agent17.F289Coverage
