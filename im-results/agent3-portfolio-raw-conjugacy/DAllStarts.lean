import DSectionTransfer

namespace BB6.Portfolio

/-- A complete exact blank-origin F0 entry schedule for all six possible
    designated initial states of the shared D0 transition table. -/
def startTime (s : State) : Nat :=
  match s.val with
  | 0 => 36
  | 1 => 15
  | 2 => 92
  | 3 => 15
  | 4 => 93
  | _ => 403

def startSeed (s : State) : Nat :=
  match s.val with
  | 0 => 9
  | 1 => 5
  | 2 => 15
  | 3 => 5
  | 4 => 15
  | _ => 39

def startHead (s : State) : Int :=
  match s.val with
  | 0 => -6
  | 1 => -3
  | 2 => -12
  | 3 => -3
  | 4 => -13
  | _ => -35

theorem every_blank_reaches_unary (s : State) :
    run D0 (startTime s) (some (blank s)) =
      some (F0Pure (startSeed s) (startHead s)) := by
  apply exact_blank_to_unary
  have all : ∀ s : State, finiteRun (startTime s) (some (finBlank s)) =
      some (finiteI (startSeed s) (startHead s)) := by
    set_option maxRecDepth 65536 in
      decide
  exact all s

/-- The all-time halting outcome of any of the six original blank starts is
    exactly the outcome of one unary section seed in {5,9,15,39}. -/
theorem every_blank_halts_iff_unary (s : State) :
    haltsFrom D0 s ↔ HaltsCfg D0 (F0Pure (startSeed s) 0) := by
  exact (haltsFrom_as_cfg D0 s).trans
    ((haltsCfg_after_prefix D0 (blank s)
      (F0Pure (startSeed s) (startHead s)) (startTime s)
      (every_blank_reaches_unary s)).trans
      (halts_F0Pure_shift D0 (startSeed s) (startHead s)))

theorem start_blank_B_D_same_halting :
    haltsFrom D0 (1:State) ↔ haltsFrom D0 (3:State) := by
  have hb := every_blank_halts_iff_unary (1:State)
  have hd := every_blank_halts_iff_unary (3:State)
  simpa [startSeed] using hb.trans hd.symm

theorem start_blank_C_E_same_halting :
    haltsFrom D0 (2:State) ↔ haltsFrom D0 (4:State) := by
  have hc := every_blank_halts_iff_unary (2:State)
  have he := every_blank_halts_iff_unary (4:State)
  simpa [startSeed] using hc.trans he.symm

#print axioms every_blank_reaches_unary
#print axioms every_blank_halts_iff_unary
#print axioms start_blank_B_D_same_halting
#print axioms start_blank_C_E_same_halting
end BB6.Portfolio
