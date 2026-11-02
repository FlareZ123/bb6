import DParseRLE

namespace BB6.Portfolio

/-- Two separately rooted October 16 unresolved S/T family RLE strings. -/
def STable : Machine :=
  parseRLE "1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB"

def TTable : Machine :=
  parseRLE "1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---"

/-- From the literal source table S to T, state coordinates A B C D E F
    become C A B F D E and the complete physical tape is mirrored. -/
def STPerm : StatePerm := {
  toFun := fun s => match s.val with
    | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 5 | 4 => 3 | _ => 4
  invFun := fun s => match s.val with
    | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 4 | 4 => 5 | _ => 3
  left_inv := by decide
  right_inv := by decide
}

theorem T_is_renamed_mirrored_S :
    TTable = renameMachine STPerm (reflectMachine STable) := by
  have h : ∀ state : State, ∀ bit : Bool,
      TTable state bit = (renameMachine STPerm (reflectMachine STable)) state bit := by
    decide
  funext state bit
  exact h state bit

/-- Genuine rooted blank T(A) corresponds to different S-table blank B.
    Neither rooted halting outcome is decided by this equivalence. -/
theorem T_root_halts_iff_S_start_B :
    haltsFrom TTable (0:State) ↔ haltsFrom STable (1:State) := by
  have hroot : STPerm (1:State) = (0:State) := by decide
  rw [T_is_renamed_mirrored_S, ← hroot]
  exact relabel_reflect_halts_iff STable STPerm true (1:State)

theorem T_root_haltsAt_iff_S_start_B (n : Nat) :
    haltsAt TTable (0:State) n ↔ haltsAt STable (1:State) n := by
  have hroot : STPerm (1:State) = (0:State) := by decide
  rw [T_is_renamed_mirrored_S, ← hroot]
  exact relabel_reflect_haltsAt_iff STable STPerm true (1:State) n

#print axioms T_is_renamed_mirrored_S
#print axioms T_root_halts_iff_S_start_B
#print axioms T_root_haltsAt_iff_S_start_B
end BB6.Portfolio
