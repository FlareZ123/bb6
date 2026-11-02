import MachineConjugacy

namespace BB6.Portfolio

/-- Four rooted D-family tables in the October 16, 2026 holdout snapshot.
    These definitions preserve each of the twelve literal table cells. -/
-- D0: 1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---
def D0 : Machine := fun s bit => match s.val, bit with
  | 0, false => some (true, .R, (1 : State))
  | 0, true => some (false, .R, (4 : State))
  | 1, false => some (true, .L, (2 : State))
  | 1, true => some (false, .R, (0 : State))
  | 2, false => some (true, .L, (0 : State))
  | 2, true => some (true, .L, (3 : State))
  | 3, false => some (true, .L, (2 : State))
  | 3, true => some (true, .L, (5 : State))
  | 4, false => some (false, .L, (2 : State))
  | 4, true => some (false, .L, (1 : State))
  | 5, false => some (true, .L, (4 : State))
  | _, _ => none

-- D1: 1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA
def D1 : Machine := fun s bit => match s.val, bit with
  | 0, false => some (true, .R, (1 : State))
  | 1, false => some (false, .R, (2 : State))
  | 1, true => some (false, .R, (4 : State))
  | 2, false => some (true, .R, (3 : State))
  | 2, true => some (true, .R, (5 : State))
  | 3, false => some (true, .L, (4 : State))
  | 3, true => some (false, .L, (1 : State))
  | 4, false => some (true, .R, (2 : State))
  | 4, true => some (false, .L, (3 : State))
  | 5, false => some (true, .R, (2 : State))
  | 5, true => some (true, .R, (0 : State))
  | _, _ => none

-- D2: 1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---
def D2 : Machine := fun s bit => match s.val, bit with
  | 0, false => some (true, .R, (1 : State))
  | 0, true => some (true, .R, (3 : State))
  | 1, false => some (true, .L, (2 : State))
  | 1, true => some (false, .L, (4 : State))
  | 2, false => some (true, .R, (0 : State))
  | 2, true => some (false, .L, (1 : State))
  | 3, false => some (true, .R, (0 : State))
  | 3, true => some (true, .R, (5 : State))
  | 4, false => some (false, .R, (0 : State))
  | 4, true => some (false, .R, (2 : State))
  | 5, false => some (true, .R, (4 : State))
  | _, _ => none

-- D3: 1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD---
def D3 : Machine := fun s bit => match s.val, bit with
  | 0, false => some (true, .R, (1 : State))
  | 0, true => some (false, .L, (2 : State))
  | 1, false => some (true, .R, (2 : State))
  | 1, true => some (true, .R, (4 : State))
  | 2, false => some (true, .L, (0 : State))
  | 2, true => some (false, .L, (3 : State))
  | 3, false => some (false, .R, (1 : State))
  | 3, true => some (false, .R, (0 : State))
  | 4, false => some (true, .R, (1 : State))
  | 4, true => some (true, .R, (5 : State))
  | 5, false => some (true, .R, (3 : State))
  | _, _ => none

/-- Verified state bijection D0 → D1, followed by left/right reflection. -/
def DPerm1 : StatePerm := {
  toFun := fun s => match s.val with
  | 0 => 3
  | 1 => 4
  | 2 => 2
  | 3 => 5
  | 4 => 1
  | _ => 0
  invFun := fun s => match s.val with
  | 0 => 5
  | 1 => 4
  | 2 => 2
  | 3 => 0
  | 4 => 1
  | _ => 3
  left_inv := by decide
  right_inv := by decide
}

theorem D1_table_conjugate : ∀ s : State, ∀ b : Bool,
    D1 s b = (renameMachine DPerm1 (reflectMachine D0)) s b := by
  decide

theorem D1_halts_from_blank :
    haltsFrom D1 (0 : State) ↔ haltsFrom D0 (5 : State) := by
  have htable : D1 = renameMachine DPerm1 (reflectMachine D0) := by
    funext s b
    exact D1_table_conjugate s b
  have hstart : DPerm1 (5 : State) = (0 : State) := by decide
  rw [htable, ←hstart]
  exact relabel_reflect_halts_iff D0 DPerm1 true (5 : State)

theorem D1_exact_halt_time (n : Nat) :
    haltsAt D1 (0 : State) n ↔ haltsAt D0 (5 : State) n := by
  have htable : D1 = renameMachine DPerm1 (reflectMachine D0) := by
    funext s b
    exact D1_table_conjugate s b
  have hstart : DPerm1 (5 : State) = (0 : State) := by decide
  rw [htable, ←hstart]
  exact relabel_reflect_haltsAt_iff D0 DPerm1 true (5 : State) n

#print axioms D1_halts_from_blank
#print axioms D1_exact_halt_time

/-- Verified state bijection D0 → D2, followed by left/right reflection. -/
def DPerm2 : StatePerm := {
  toFun := fun s => match s.val with
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | 3 => 3
  | 4 => 4
  | _ => 5
  invFun := fun s => match s.val with
  | 0 => 2
  | 1 => 0
  | 2 => 1
  | 3 => 3
  | 4 => 4
  | _ => 5
  left_inv := by decide
  right_inv := by decide
}

theorem D2_table_conjugate : ∀ s : State, ∀ b : Bool,
    D2 s b = (renameMachine DPerm2 (reflectMachine D0)) s b := by
  decide

theorem D2_halts_from_blank :
    haltsFrom D2 (0 : State) ↔ haltsFrom D0 (2 : State) := by
  have htable : D2 = renameMachine DPerm2 (reflectMachine D0) := by
    funext s b
    exact D2_table_conjugate s b
  have hstart : DPerm2 (2 : State) = (0 : State) := by decide
  rw [htable, ←hstart]
  exact relabel_reflect_halts_iff D0 DPerm2 true (2 : State)

theorem D2_exact_halt_time (n : Nat) :
    haltsAt D2 (0 : State) n ↔ haltsAt D0 (2 : State) n := by
  have htable : D2 = renameMachine DPerm2 (reflectMachine D0) := by
    funext s b
    exact D2_table_conjugate s b
  have hstart : DPerm2 (2 : State) = (0 : State) := by decide
  rw [htable, ←hstart]
  exact relabel_reflect_haltsAt_iff D0 DPerm2 true (2 : State) n

#print axioms D2_halts_from_blank
#print axioms D2_exact_halt_time

/-- Verified state bijection D0 → D3, followed by left/right reflection. -/
def DPerm3 : StatePerm := {
  toFun := fun s => match s.val with
  | 0 => 2
  | 1 => 0
  | 2 => 1
  | 3 => 4
  | 4 => 3
  | _ => 5
  invFun := fun s => match s.val with
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | 3 => 4
  | 4 => 3
  | _ => 5
  left_inv := by decide
  right_inv := by decide
}

theorem D3_table_conjugate : ∀ s : State, ∀ b : Bool,
    D3 s b = (renameMachine DPerm3 (reflectMachine D0)) s b := by
  decide

theorem D3_halts_from_blank :
    haltsFrom D3 (0 : State) ↔ haltsFrom D0 (1 : State) := by
  have htable : D3 = renameMachine DPerm3 (reflectMachine D0) := by
    funext s b
    exact D3_table_conjugate s b
  have hstart : DPerm3 (1 : State) = (0 : State) := by decide
  rw [htable, ←hstart]
  exact relabel_reflect_halts_iff D0 DPerm3 true (1 : State)

theorem D3_exact_halt_time (n : Nat) :
    haltsAt D3 (0 : State) n ↔ haltsAt D0 (1 : State) n := by
  have htable : D3 = renameMachine DPerm3 (reflectMachine D0) := by
    funext s b
    exact D3_table_conjugate s b
  have hstart : DPerm3 (1 : State) = (0 : State) := by decide
  rw [htable, ←hstart]
  exact relabel_reflect_haltsAt_iff D0 DPerm3 true (1 : State) n

#print axioms D3_halts_from_blank
#print axioms D3_exact_halt_time

end BB6.Portfolio
