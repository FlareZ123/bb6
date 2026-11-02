import DParseRLE

namespace BB6.Portfolio

/-- The two distinct rooted S/T holdouts in the pinned 2026-10-16 BB(6)
    catalogue, decoded directly from their complete literal RLE strings. -/
def SRoot : Machine :=
  parseRLE "1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB"

def TRoot : Machine :=
  parseRLE "1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---"

/-- SRoot state-name coordinates map A,B,C,D,E,F to C,A,B,F,D,E
    in TRoot. A full physical left/right reflection is also necessary. -/
def STPerm : StatePerm := {
  toFun := fun s => match s.val with
    | 0 => 2
    | 1 => 0
    | 2 => 1
    | 3 => 5
    | 4 => 3
    | _ => 4
  invFun := fun s => match s.val with
    | 0 => 1
    | 1 => 2
    | 2 => 0
    | 3 => 4
    | 4 => 5
    | _ => 3
  left_inv := by decide
  right_inv := by decide
}

/-- Checks all 12 source transition entries, including the absent halt cell. -/
theorem ST_table_conjugate : ∀ s : State, ∀ b : Bool,
    TRoot s b = (renameMachine STPerm (reflectMachine SRoot)) s b := by
  decide

theorem ST_blank_rooted_halts_iff :
    haltsFrom TRoot (0 : State) ↔ haltsFrom SRoot (1 : State) := by
  have htable : TRoot = renameMachine STPerm (reflectMachine SRoot) := by
    funext s b
    exact ST_table_conjugate s b
  have hstart : STPerm (1 : State) = (0 : State) := by decide
  rw [htable, ← hstart]
  exact relabel_reflect_halts_iff SRoot STPerm true (1 : State)

/-- The two blank-origin runs have exactly equal raw halting-time predicates
    after assigning SRoot's B, rather than A, as its starting state. -/
theorem ST_blank_rooted_haltsAt_iff (n : Nat) :
    haltsAt TRoot (0 : State) n ↔ haltsAt SRoot (1 : State) n := by
  have htable : TRoot = renameMachine STPerm (reflectMachine SRoot) := by
    funext s b
    exact ST_table_conjugate s b
  have hstart : STPerm (1 : State) = (0 : State) := by decide
  rw [htable, ← hstart]
  exact relabel_reflect_haltsAt_iff SRoot STPerm true (1 : State) n

#print axioms ST_table_conjugate
#print axioms ST_blank_rooted_halts_iff
#print axioms ST_blank_rooted_haltsAt_iff

end BB6.Portfolio
