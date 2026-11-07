import GenericOverwrite
import Lean.Elab.Tactic.Omega

/-!
Finite explicit original-format six-state RLE tables from frozen 2026-10-16
663 historic holdouts. Each entry has one specified incoming halting-state
transition which the proven generic last-write theorem excludes for all
blank-root times. No original machine is decided by these exclusions.
The source data file is resources/BB6_holdouts_663_2026-10-16.txt.
-/

namespace BB6Overwrite
open BB6Coverage

/-- Holdout #9: 1RB0LE_1RC---_0RD0RB_1RE0LA_1RF0LF_1LD1RF
Blocked immediate predecessor A/0 -> B/1;
there are 2 total input rows entering its halting state. -/
def root9 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, false, ⟨4, by decide⟩⟩
  | 1, false => some ⟨true, true, ⟨2, by decide⟩⟩
  | 1, true => none
  | 2, false => some ⟨false, true, ⟨3, by decide⟩⟩
  | 2, true => some ⟨false, true, ⟨1, by decide⟩⟩
  | 3, false => some ⟨true, true, ⟨4, by decide⟩⟩
  | 3, true => some ⟨false, false, ⟨0, by decide⟩⟩
  | 4, false => some ⟨true, true, ⟨5, by decide⟩⟩
  | 4, true => some ⟨false, false, ⟨5, by decide⟩⟩
  | 5, false => some ⟨true, false, ⟨3, by decide⟩⟩
  | 5, true => some ⟨true, true, ⟨5, by decide⟩⟩
  | _, _ => none

private theorem root9_entry :
    ∀ (s : Slot) (t : Move), root9 s = some t →
      t.next = ⟨0, by decide⟩ →
      t.write = false ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root9] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root9_forbidden_parent (n : Nat) (c : Config)
    (hr : run root9 n blank = some c)
    (hs : readSlot c = (⟨0, by decide⟩, false)) :
    ∃ d, rawStep root9 c = some d ∧
      d.state = ⟨1, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root9 ⟨0, by decide⟩ false
    true true ⟨1, by decide⟩ true
    (by decide) root9_entry (by decide) n c hr hs

#print axioms root9_forbidden_parent

/-- Holdout #31: 1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB
Blocked immediate predecessor F/1 -> B/1;
there are 2 total input rows entering its halting state. -/
def root31 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨true, true, ⟨4, by decide⟩⟩
  | 1, false => some ⟨false, true, ⟨2, by decide⟩⟩
  | 1, true => none
  | 2, false => some ⟨true, true, ⟨3, by decide⟩⟩
  | 2, true => some ⟨false, true, ⟨3, by decide⟩⟩
  | 3, false => some ⟨true, false, ⟨4, by decide⟩⟩
  | 3, true => some ⟨false, false, ⟨5, by decide⟩⟩
  | 4, false => some ⟨true, true, ⟨0, by decide⟩⟩
  | 4, true => some ⟨false, false, ⟨3, by decide⟩⟩
  | 5, false => some ⟨true, false, ⟨2, by decide⟩⟩
  | 5, true => some ⟨true, true, ⟨1, by decide⟩⟩
  | _, _ => none

private theorem root31_entry :
    ∀ (s : Slot) (t : Move), root31 s = some t →
      t.next = ⟨5, by decide⟩ →
      t.write = false ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root31] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root31_forbidden_parent (n : Nat) (c : Config)
    (hr : run root31 n blank = some c)
    (hs : readSlot c = (⟨5, by decide⟩, true)) :
    ∃ d, rawStep root31 c = some d ∧
      d.state = ⟨1, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root31 ⟨5, by decide⟩ true
    true true ⟨1, by decide⟩ true
    (by decide) root31_entry (by decide) n c hr hs

#print axioms root31_forbidden_parent

/-- Holdout #45: 1RB0RF_1LC0RA_1LD1LB_0LE---_1LA0LA_1RE1LD
Blocked immediate predecessor F/1 -> D/1;
there are 2 total input rows entering its halting state. -/
def root45 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, true, ⟨5, by decide⟩⟩
  | 1, false => some ⟨true, false, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, true, ⟨0, by decide⟩⟩
  | 2, false => some ⟨true, false, ⟨3, by decide⟩⟩
  | 2, true => some ⟨true, false, ⟨1, by decide⟩⟩
  | 3, false => some ⟨false, false, ⟨4, by decide⟩⟩
  | 3, true => none
  | 4, false => some ⟨true, false, ⟨0, by decide⟩⟩
  | 4, true => some ⟨false, false, ⟨0, by decide⟩⟩
  | 5, false => some ⟨true, true, ⟨4, by decide⟩⟩
  | 5, true => some ⟨true, false, ⟨3, by decide⟩⟩
  | _, _ => none

private theorem root45_entry :
    ∀ (s : Slot) (t : Move), root45 s = some t →
      t.next = ⟨5, by decide⟩ →
      t.write = false ∧ t.right = true := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root45] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root45_forbidden_parent (n : Nat) (c : Config)
    (hr : run root45 n blank = some c)
    (hs : readSlot c = (⟨5, by decide⟩, true)) :
    ∃ d, rawStep root45 c = some d ∧
      d.state = ⟨3, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root45 ⟨5, by decide⟩ true
    false true ⟨3, by decide⟩ true
    (by decide) root45_entry (by decide) n c hr hs

#print axioms root45_forbidden_parent

/-- Holdout #52: 1RB1LD_1LC0RD_0LA0RB_0LE1LF_1RF0LC_0RB---
Blocked immediate predecessor E/0 -> F/1;
there are 2 total input rows entering its halting state. -/
def root52 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨true, false, ⟨3, by decide⟩⟩
  | 1, false => some ⟨true, false, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, true, ⟨3, by decide⟩⟩
  | 2, false => some ⟨false, false, ⟨0, by decide⟩⟩
  | 2, true => some ⟨false, true, ⟨1, by decide⟩⟩
  | 3, false => some ⟨false, false, ⟨4, by decide⟩⟩
  | 3, true => some ⟨true, false, ⟨5, by decide⟩⟩
  | 4, false => some ⟨true, true, ⟨5, by decide⟩⟩
  | 4, true => some ⟨false, false, ⟨2, by decide⟩⟩
  | 5, false => some ⟨false, true, ⟨1, by decide⟩⟩
  | 5, true => none
  | _, _ => none

private theorem root52_entry :
    ∀ (s : Slot) (t : Move), root52 s = some t →
      t.next = ⟨4, by decide⟩ →
      t.write = false ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root52] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root52_forbidden_parent (n : Nat) (c : Config)
    (hr : run root52 n blank = some c)
    (hs : readSlot c = (⟨4, by decide⟩, false)) :
    ∃ d, rawStep root52 c = some d ∧
      d.state = ⟨5, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root52 ⟨4, by decide⟩ false
    true true ⟨5, by decide⟩ true
    (by decide) root52_entry (by decide) n c hr hs

#print axioms root52_forbidden_parent

/-- Holdout #66: 1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE
Blocked immediate predecessor C/0 -> D/0;
there are 2 total input rows entering its halting state. -/
def root66 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, false, ⟨5, by decide⟩⟩
  | 1, false => some ⟨true, false, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, false, ⟨3, by decide⟩⟩
  | 2, false => some ⟨true, true, ⟨3, by decide⟩⟩
  | 2, true => some ⟨true, false, ⟨1, by decide⟩⟩
  | 3, false => none
  | 3, true => some ⟨true, true, ⟨4, by decide⟩⟩
  | 4, false => some ⟨false, true, ⟨0, by decide⟩⟩
  | 4, true => some ⟨true, true, ⟨4, by decide⟩⟩
  | 5, false => some ⟨true, false, ⟨0, by decide⟩⟩
  | 5, true => some ⟨false, false, ⟨4, by decide⟩⟩
  | _, _ => none

private theorem root66_entry :
    ∀ (s : Slot) (t : Move), root66 s = some t →
      t.next = ⟨2, by decide⟩ →
      t.write = true ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root66] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root66_forbidden_parent (n : Nat) (c : Config)
    (hr : run root66 n blank = some c)
    (hs : readSlot c = (⟨2, by decide⟩, false)) :
    ∃ d, rawStep root66 c = some d ∧
      d.state = ⟨3, by decide⟩ ∧ d.tape d.head ≠ false := by
  exact forbidden_transition root66 ⟨2, by decide⟩ false
    true false ⟨3, by decide⟩ true
    (by decide) root66_entry (by decide) n c hr hs

#print axioms root66_forbidden_parent

/-- Holdout #71: 1RB0RC_1RC---_1LD1RE_1LE0LD_1RA0LF_0RC0RB
Blocked immediate predecessor F/1 -> B/1;
there are 2 total input rows entering its halting state. -/
def root71 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, true, ⟨2, by decide⟩⟩
  | 1, false => some ⟨true, true, ⟨2, by decide⟩⟩
  | 1, true => none
  | 2, false => some ⟨true, false, ⟨3, by decide⟩⟩
  | 2, true => some ⟨true, true, ⟨4, by decide⟩⟩
  | 3, false => some ⟨true, false, ⟨4, by decide⟩⟩
  | 3, true => some ⟨false, false, ⟨3, by decide⟩⟩
  | 4, false => some ⟨true, true, ⟨0, by decide⟩⟩
  | 4, true => some ⟨false, false, ⟨5, by decide⟩⟩
  | 5, false => some ⟨false, true, ⟨2, by decide⟩⟩
  | 5, true => some ⟨false, true, ⟨1, by decide⟩⟩
  | _, _ => none

private theorem root71_entry :
    ∀ (s : Slot) (t : Move), root71 s = some t →
      t.next = ⟨5, by decide⟩ →
      t.write = false ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root71] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root71_forbidden_parent (n : Nat) (c : Config)
    (hr : run root71 n blank = some c)
    (hs : readSlot c = (⟨5, by decide⟩, true)) :
    ∃ d, rawStep root71 c = some d ∧
      d.state = ⟨1, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root71 ⟨5, by decide⟩ true
    true true ⟨1, by decide⟩ false
    (by decide) root71_entry (by decide) n c hr hs

#print axioms root71_forbidden_parent

/-- Holdout #76: 1RB0LD_1RC0RF_0LD0LE_1RF1LC_0LB1LE_0RA---
Blocked immediate predecessor D/0 -> F/1;
there are 2 total input rows entering its halting state. -/
def root76 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, false, ⟨3, by decide⟩⟩
  | 1, false => some ⟨true, true, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, true, ⟨5, by decide⟩⟩
  | 2, false => some ⟨false, false, ⟨3, by decide⟩⟩
  | 2, true => some ⟨false, false, ⟨4, by decide⟩⟩
  | 3, false => some ⟨true, true, ⟨5, by decide⟩⟩
  | 3, true => some ⟨true, false, ⟨2, by decide⟩⟩
  | 4, false => some ⟨false, false, ⟨1, by decide⟩⟩
  | 4, true => some ⟨true, false, ⟨4, by decide⟩⟩
  | 5, false => some ⟨false, true, ⟨0, by decide⟩⟩
  | 5, true => none
  | _, _ => none

private theorem root76_entry :
    ∀ (s : Slot) (t : Move), root76 s = some t →
      t.next = ⟨3, by decide⟩ →
      t.write = false ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root76] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root76_forbidden_parent (n : Nat) (c : Config)
    (hr : run root76 n blank = some c)
    (hs : readSlot c = (⟨3, by decide⟩, false)) :
    ∃ d, rawStep root76 c = some d ∧
      d.state = ⟨5, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root76 ⟨3, by decide⟩ false
    true true ⟨5, by decide⟩ true
    (by decide) root76_entry (by decide) n c hr hs

#print axioms root76_forbidden_parent

/-- Holdout #105: 1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD
Blocked immediate predecessor C/0 -> D/0;
there are 2 total input rows entering its halting state. -/
def root105 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨true, false, ⟨4, by decide⟩⟩
  | 1, false => some ⟨true, false, ⟨1, by decide⟩⟩
  | 1, true => some ⟨true, false, ⟨2, by decide⟩⟩
  | 2, false => some ⟨true, true, ⟨3, by decide⟩⟩
  | 2, true => some ⟨false, false, ⟨4, by decide⟩⟩
  | 3, false => none
  | 3, true => some ⟨false, true, ⟨1, by decide⟩⟩
  | 4, false => some ⟨true, true, ⟨5, by decide⟩⟩
  | 4, true => some ⟨true, false, ⟨0, by decide⟩⟩
  | 5, false => some ⟨false, true, ⟨0, by decide⟩⟩
  | 5, true => some ⟨false, true, ⟨3, by decide⟩⟩
  | _, _ => none

private theorem root105_entry :
    ∀ (s : Slot) (t : Move), root105 s = some t →
      t.next = ⟨2, by decide⟩ →
      t.write = true ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root105] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root105_forbidden_parent (n : Nat) (c : Config)
    (hr : run root105 n blank = some c)
    (hs : readSlot c = (⟨2, by decide⟩, false)) :
    ∃ d, rawStep root105 c = some d ∧
      d.state = ⟨3, by decide⟩ ∧ d.tape d.head ≠ false := by
  exact forbidden_transition root105 ⟨2, by decide⟩ false
    true false ⟨3, by decide⟩ true
    (by decide) root105_entry (by decide) n c hr hs

#print axioms root105_forbidden_parent

/-- Holdout #110: 1RB1RA_1LC0RA_1LD0LC_0LE0LB_1LF1RF_1LA---
Blocked immediate predecessor E/1 -> F/1;
there are 2 total input rows entering its halting state. -/
def root110 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨true, true, ⟨0, by decide⟩⟩
  | 1, false => some ⟨true, false, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, true, ⟨0, by decide⟩⟩
  | 2, false => some ⟨true, false, ⟨3, by decide⟩⟩
  | 2, true => some ⟨false, false, ⟨2, by decide⟩⟩
  | 3, false => some ⟨false, false, ⟨4, by decide⟩⟩
  | 3, true => some ⟨false, false, ⟨1, by decide⟩⟩
  | 4, false => some ⟨true, false, ⟨5, by decide⟩⟩
  | 4, true => some ⟨true, true, ⟨5, by decide⟩⟩
  | 5, false => some ⟨true, false, ⟨0, by decide⟩⟩
  | 5, true => none
  | _, _ => none

private theorem root110_entry :
    ∀ (s : Slot) (t : Move), root110 s = some t →
      t.next = ⟨4, by decide⟩ →
      t.write = false ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root110] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root110_forbidden_parent (n : Nat) (c : Config)
    (hr : run root110 n blank = some c)
    (hs : readSlot c = (⟨4, by decide⟩, true)) :
    ∃ d, rawStep root110 c = some d ∧
      d.state = ⟨5, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root110 ⟨4, by decide⟩ true
    true true ⟨5, by decide⟩ true
    (by decide) root110_entry (by decide) n c hr hs

#print axioms root110_forbidden_parent

/-- Holdout #132: 1RB1LB_1RC---_1LD1LF_1LE0LD_0LA1RF_1LC0RE
Blocked immediate predecessor A/0 -> B/1;
there are 2 total input rows entering its halting state. -/
def root132 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨true, false, ⟨1, by decide⟩⟩
  | 1, false => some ⟨true, true, ⟨2, by decide⟩⟩
  | 1, true => none
  | 2, false => some ⟨true, false, ⟨3, by decide⟩⟩
  | 2, true => some ⟨true, false, ⟨5, by decide⟩⟩
  | 3, false => some ⟨true, false, ⟨4, by decide⟩⟩
  | 3, true => some ⟨false, false, ⟨3, by decide⟩⟩
  | 4, false => some ⟨false, false, ⟨0, by decide⟩⟩
  | 4, true => some ⟨true, true, ⟨5, by decide⟩⟩
  | 5, false => some ⟨true, false, ⟨2, by decide⟩⟩
  | 5, true => some ⟨false, true, ⟨4, by decide⟩⟩
  | _, _ => none

private theorem root132_entry :
    ∀ (s : Slot) (t : Move), root132 s = some t →
      t.next = ⟨0, by decide⟩ →
      t.write = false ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root132] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root132_forbidden_parent (n : Nat) (c : Config)
    (hr : run root132 n blank = some c)
    (hs : readSlot c = (⟨0, by decide⟩, false)) :
    ∃ d, rawStep root132 c = some d ∧
      d.state = ⟨1, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root132 ⟨0, by decide⟩ false
    true true ⟨1, by decide⟩ true
    (by decide) root132_entry (by decide) n c hr hs

#print axioms root132_forbidden_parent

/-- Holdout #135: 1RB0LC_0LA1RD_1LA0RE_1RE0RF_1LF---_1LB1RF
Blocked immediate predecessor C/1 -> E/1;
there are 2 total input rows entering its halting state. -/
def root135 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, false, ⟨2, by decide⟩⟩
  | 1, false => some ⟨false, false, ⟨0, by decide⟩⟩
  | 1, true => some ⟨true, true, ⟨3, by decide⟩⟩
  | 2, false => some ⟨true, false, ⟨0, by decide⟩⟩
  | 2, true => some ⟨false, true, ⟨4, by decide⟩⟩
  | 3, false => some ⟨true, true, ⟨4, by decide⟩⟩
  | 3, true => some ⟨false, true, ⟨5, by decide⟩⟩
  | 4, false => some ⟨true, false, ⟨5, by decide⟩⟩
  | 4, true => none
  | 5, false => some ⟨true, false, ⟨1, by decide⟩⟩
  | 5, true => some ⟨true, true, ⟨5, by decide⟩⟩
  | _, _ => none

private theorem root135_entry :
    ∀ (s : Slot) (t : Move), root135 s = some t →
      t.next = ⟨2, by decide⟩ →
      t.write = false ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root135] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root135_forbidden_parent (n : Nat) (c : Config)
    (hr : run root135 n blank = some c)
    (hs : readSlot c = (⟨2, by decide⟩, true)) :
    ∃ d, rawStep root135 c = some d ∧
      d.state = ⟨4, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root135 ⟨2, by decide⟩ true
    true true ⟨4, by decide⟩ false
    (by decide) root135_entry (by decide) n c hr hs

#print axioms root135_forbidden_parent

/-- Holdout #142: 1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---
Blocked immediate predecessor E/1 -> F/1;
there are 2 total input rows entering its halting state. -/
def root142 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, true, ⟨0, by decide⟩⟩
  | 1, false => some ⟨true, false, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, true, ⟨4, by decide⟩⟩
  | 2, false => some ⟨false, false, ⟨3, by decide⟩⟩
  | 2, true => some ⟨false, false, ⟨1, by decide⟩⟩
  | 3, false => some ⟨true, false, ⟨0, by decide⟩⟩
  | 3, true => some ⟨true, false, ⟨5, by decide⟩⟩
  | 4, false => some ⟨true, true, ⟨0, by decide⟩⟩
  | 4, true => some ⟨false, false, ⟨5, by decide⟩⟩
  | 5, false => some ⟨true, false, ⟨2, by decide⟩⟩
  | 5, true => none
  | _, _ => none

private theorem root142_entry :
    ∀ (s : Slot) (t : Move), root142 s = some t →
      t.next = ⟨4, by decide⟩ →
      t.write = false ∧ t.right = true := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root142] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root142_forbidden_parent (n : Nat) (c : Config)
    (hr : run root142 n blank = some c)
    (hs : readSlot c = (⟨4, by decide⟩, true)) :
    ∃ d, rawStep root142 c = some d ∧
      d.state = ⟨5, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root142 ⟨4, by decide⟩ true
    false true ⟨5, by decide⟩ false
    (by decide) root142_entry (by decide) n c hr hs

#print axioms root142_forbidden_parent

/-- Holdout #144: 1RB1RF_1RC0RF_0RD0LC_1LE1RA_1LC---_1RB0RE
Blocked immediate predecessor D/0 -> E/1;
there are 2 total input rows entering its halting state. -/
def root144 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨true, true, ⟨5, by decide⟩⟩
  | 1, false => some ⟨true, true, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, true, ⟨5, by decide⟩⟩
  | 2, false => some ⟨false, true, ⟨3, by decide⟩⟩
  | 2, true => some ⟨false, false, ⟨2, by decide⟩⟩
  | 3, false => some ⟨true, false, ⟨4, by decide⟩⟩
  | 3, true => some ⟨true, true, ⟨0, by decide⟩⟩
  | 4, false => some ⟨true, false, ⟨2, by decide⟩⟩
  | 4, true => none
  | 5, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 5, true => some ⟨false, true, ⟨4, by decide⟩⟩
  | _, _ => none

private theorem root144_entry :
    ∀ (s : Slot) (t : Move), root144 s = some t →
      t.next = ⟨3, by decide⟩ →
      t.write = false ∧ t.right = true := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root144] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root144_forbidden_parent (n : Nat) (c : Config)
    (hr : run root144 n blank = some c)
    (hs : readSlot c = (⟨3, by decide⟩, false)) :
    ∃ d, rawStep root144 c = some d ∧
      d.state = ⟨4, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root144 ⟨3, by decide⟩ false
    false true ⟨4, by decide⟩ true
    (by decide) root144_entry (by decide) n c hr hs

#print axioms root144_forbidden_parent

/-- Holdout #159: 1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF
Blocked immediate predecessor C/1 -> D/1;
there are 2 total input rows entering its halting state. -/
def root159 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, false, ⟨4, by decide⟩⟩
  | 1, false => some ⟨false, false, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, true, ⟨0, by decide⟩⟩
  | 2, false => some ⟨true, false, ⟨4, by decide⟩⟩
  | 2, true => some ⟨false, true, ⟨3, by decide⟩⟩
  | 3, false => some ⟨false, true, ⟨1, by decide⟩⟩
  | 3, true => none
  | 4, false => some ⟨false, false, ⟨5, by decide⟩⟩
  | 4, true => some ⟨false, false, ⟨3, by decide⟩⟩
  | 5, false => some ⟨true, false, ⟨0, by decide⟩⟩
  | 5, true => some ⟨false, false, ⟨5, by decide⟩⟩
  | _, _ => none

private theorem root159_entry :
    ∀ (s : Slot) (t : Move), root159 s = some t →
      t.next = ⟨2, by decide⟩ →
      t.write = false ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root159] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root159_forbidden_parent (n : Nat) (c : Config)
    (hr : run root159 n blank = some c)
    (hs : readSlot c = (⟨2, by decide⟩, true)) :
    ∃ d, rawStep root159 c = some d ∧
      d.state = ⟨3, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root159 ⟨2, by decide⟩ true
    true true ⟨3, by decide⟩ false
    (by decide) root159_entry (by decide) n c hr hs

#print axioms root159_forbidden_parent

/-- Holdout #173: 1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE---
Blocked immediate predecessor D/1 -> F/1;
there are 2 total input rows entering its halting state. -/
def root173 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨true, true, ⟨5, by decide⟩⟩
  | 1, false => some ⟨true, false, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, false, ⟨1, by decide⟩⟩
  | 2, false => some ⟨true, true, ⟨4, by decide⟩⟩
  | 2, true => some ⟨false, false, ⟨3, by decide⟩⟩
  | 3, false => some ⟨true, false, ⟨1, by decide⟩⟩
  | 3, true => some ⟨false, true, ⟨5, by decide⟩⟩
  | 4, false => some ⟨false, true, ⟨0, by decide⟩⟩
  | 4, true => some ⟨false, true, ⟨2, by decide⟩⟩
  | 5, false => some ⟨true, true, ⟨4, by decide⟩⟩
  | 5, true => none
  | _, _ => none

private theorem root173_entry :
    ∀ (s : Slot) (t : Move), root173 s = some t →
      t.next = ⟨3, by decide⟩ →
      t.write = false ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root173] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root173_forbidden_parent (n : Nat) (c : Config)
    (hr : run root173 n blank = some c)
    (hs : readSlot c = (⟨3, by decide⟩, true)) :
    ∃ d, rawStep root173 c = some d ∧
      d.state = ⟨5, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root173 ⟨3, by decide⟩ true
    true true ⟨5, by decide⟩ false
    (by decide) root173_entry (by decide) n c hr hs

#print axioms root173_forbidden_parent

/-- Holdout #182: 1RB0RF_0LC---_1LE1LD_1RE0LA_1RA0RD_1LB1RD
Blocked immediate predecessor F/0 -> B/1;
there are 2 total input rows entering its halting state. -/
def root182 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, true, ⟨5, by decide⟩⟩
  | 1, false => some ⟨false, false, ⟨2, by decide⟩⟩
  | 1, true => none
  | 2, false => some ⟨true, false, ⟨4, by decide⟩⟩
  | 2, true => some ⟨true, false, ⟨3, by decide⟩⟩
  | 3, false => some ⟨true, true, ⟨4, by decide⟩⟩
  | 3, true => some ⟨false, false, ⟨0, by decide⟩⟩
  | 4, false => some ⟨true, true, ⟨0, by decide⟩⟩
  | 4, true => some ⟨false, true, ⟨3, by decide⟩⟩
  | 5, false => some ⟨true, false, ⟨1, by decide⟩⟩
  | 5, true => some ⟨true, true, ⟨3, by decide⟩⟩
  | _, _ => none

private theorem root182_entry :
    ∀ (s : Slot) (t : Move), root182 s = some t →
      t.next = ⟨5, by decide⟩ →
      t.write = false ∧ t.right = true := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root182] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root182_forbidden_parent (n : Nat) (c : Config)
    (hr : run root182 n blank = some c)
    (hs : readSlot c = (⟨5, by decide⟩, false)) :
    ∃ d, rawStep root182 c = some d ∧
      d.state = ⟨1, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root182 ⟨5, by decide⟩ false
    false true ⟨1, by decide⟩ true
    (by decide) root182_entry (by decide) n c hr hs

#print axioms root182_forbidden_parent

/-- Holdout #191: 1RB0LA_0RC1LF_0RD0LA_1LD0LE_1RB1LF_---1LA
Blocked immediate predecessor B/1 -> F/0;
there are 2 total input rows entering its halting state. -/
def root191 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, false, ⟨0, by decide⟩⟩
  | 1, false => some ⟨false, true, ⟨2, by decide⟩⟩
  | 1, true => some ⟨true, false, ⟨5, by decide⟩⟩
  | 2, false => some ⟨false, true, ⟨3, by decide⟩⟩
  | 2, true => some ⟨false, false, ⟨0, by decide⟩⟩
  | 3, false => some ⟨true, false, ⟨3, by decide⟩⟩
  | 3, true => some ⟨false, false, ⟨4, by decide⟩⟩
  | 4, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 4, true => some ⟨true, false, ⟨5, by decide⟩⟩
  | 5, false => none
  | 5, true => some ⟨true, false, ⟨0, by decide⟩⟩
  | _, _ => none

private theorem root191_entry :
    ∀ (s : Slot) (t : Move), root191 s = some t →
      t.next = ⟨1, by decide⟩ →
      t.write = true ∧ t.right = true := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root191] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root191_forbidden_parent (n : Nat) (c : Config)
    (hr : run root191 n blank = some c)
    (hs : readSlot c = (⟨1, by decide⟩, true)) :
    ∃ d, rawStep root191 c = some d ∧
      d.state = ⟨5, by decide⟩ ∧ d.tape d.head ≠ false := by
  exact forbidden_transition root191 ⟨1, by decide⟩ true
    false false ⟨5, by decide⟩ true
    (by decide) root191_entry (by decide) n c hr hs

#print axioms root191_forbidden_parent

/-- Holdout #204: 1RB0RF_1LC0RC_0LD1LC_1RE1LB_1RF---_1LE1RA
Blocked immediate predecessor D/0 -> E/1;
there are 2 total input rows entering its halting state. -/
def root204 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, true, ⟨5, by decide⟩⟩
  | 1, false => some ⟨true, false, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, true, ⟨2, by decide⟩⟩
  | 2, false => some ⟨false, false, ⟨3, by decide⟩⟩
  | 2, true => some ⟨true, false, ⟨2, by decide⟩⟩
  | 3, false => some ⟨true, true, ⟨4, by decide⟩⟩
  | 3, true => some ⟨true, false, ⟨1, by decide⟩⟩
  | 4, false => some ⟨true, true, ⟨5, by decide⟩⟩
  | 4, true => none
  | 5, false => some ⟨true, false, ⟨4, by decide⟩⟩
  | 5, true => some ⟨true, true, ⟨0, by decide⟩⟩
  | _, _ => none

private theorem root204_entry :
    ∀ (s : Slot) (t : Move), root204 s = some t →
      t.next = ⟨3, by decide⟩ →
      t.write = false ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root204] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root204_forbidden_parent (n : Nat) (c : Config)
    (hr : run root204 n blank = some c)
    (hs : readSlot c = (⟨3, by decide⟩, false)) :
    ∃ d, rawStep root204 c = some d ∧
      d.state = ⟨4, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root204 ⟨3, by decide⟩ false
    true true ⟨4, by decide⟩ true
    (by decide) root204_entry (by decide) n c hr hs

#print axioms root204_forbidden_parent

/-- Holdout #232: 1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB
Blocked immediate predecessor C/0 -> D/0;
there are 2 total input rows entering its halting state. -/
def root232 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨true, false, ⟨2, by decide⟩⟩
  | 1, false => some ⟨true, false, ⟨0, by decide⟩⟩
  | 1, true => some ⟨true, true, ⟨4, by decide⟩⟩
  | 2, false => some ⟨false, true, ⟨3, by decide⟩⟩
  | 2, true => some ⟨false, false, ⟨0, by decide⟩⟩
  | 3, false => none
  | 3, true => some ⟨true, false, ⟨1, by decide⟩⟩
  | 4, false => some ⟨true, false, ⟨3, by decide⟩⟩
  | 4, true => some ⟨false, true, ⟨5, by decide⟩⟩
  | 5, false => some ⟨false, true, ⟨4, by decide⟩⟩
  | 5, true => some ⟨true, true, ⟨1, by decide⟩⟩
  | _, _ => none

private theorem root232_entry :
    ∀ (s : Slot) (t : Move), root232 s = some t →
      t.next = ⟨2, by decide⟩ →
      t.write = true ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root232] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root232_forbidden_parent (n : Nat) (c : Config)
    (hr : run root232 n blank = some c)
    (hs : readSlot c = (⟨2, by decide⟩, false)) :
    ∃ d, rawStep root232 c = some d ∧
      d.state = ⟨3, by decide⟩ ∧ d.tape d.head ≠ false := by
  exact forbidden_transition root232 ⟨2, by decide⟩ false
    true false ⟨3, by decide⟩ false
    (by decide) root232_entry (by decide) n c hr hs

#print axioms root232_forbidden_parent

/-- Holdout #233: 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE
Blocked immediate predecessor F/1 -> E/1;
there are 2 total input rows entering its halting state. -/
def root233 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨true, true, ⟨0, by decide⟩⟩
  | 1, false => some ⟨true, false, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, true, ⟨3, by decide⟩⟩
  | 2, false => some ⟨true, false, ⟨3, by decide⟩⟩
  | 2, true => some ⟨true, false, ⟨1, by decide⟩⟩
  | 3, false => some ⟨true, false, ⟨4, by decide⟩⟩
  | 3, true => some ⟨false, false, ⟨5, by decide⟩⟩
  | 4, false => some ⟨false, true, ⟨0, by decide⟩⟩
  | 4, true => none
  | 5, false => some ⟨false, false, ⟨1, by decide⟩⟩
  | 5, true => some ⟨true, true, ⟨4, by decide⟩⟩
  | _, _ => none

private theorem root233_entry :
    ∀ (s : Slot) (t : Move), root233 s = some t →
      t.next = ⟨5, by decide⟩ →
      t.write = false ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root233] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root233_forbidden_parent (n : Nat) (c : Config)
    (hr : run root233 n blank = some c)
    (hs : readSlot c = (⟨5, by decide⟩, true)) :
    ∃ d, rawStep root233 c = some d ∧
      d.state = ⟨4, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root233 ⟨5, by decide⟩ true
    true true ⟨4, by decide⟩ true
    (by decide) root233_entry (by decide) n c hr hs

#print axioms root233_forbidden_parent

/-- Holdout #278: 1RB---_0RC0RD_1LD0RF_0LE0LC_1RA0LC_1RC0RA
Blocked immediate predecessor E/0 -> A/1;
there are 2 total input rows entering its halting state. -/
def root278 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => none
  | 1, false => some ⟨false, true, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, true, ⟨3, by decide⟩⟩
  | 2, false => some ⟨true, false, ⟨3, by decide⟩⟩
  | 2, true => some ⟨false, true, ⟨5, by decide⟩⟩
  | 3, false => some ⟨false, false, ⟨4, by decide⟩⟩
  | 3, true => some ⟨false, false, ⟨2, by decide⟩⟩
  | 4, false => some ⟨true, true, ⟨0, by decide⟩⟩
  | 4, true => some ⟨false, false, ⟨2, by decide⟩⟩
  | 5, false => some ⟨true, true, ⟨2, by decide⟩⟩
  | 5, true => some ⟨false, true, ⟨0, by decide⟩⟩
  | _, _ => none

private theorem root278_entry :
    ∀ (s : Slot) (t : Move), root278 s = some t →
      t.next = ⟨4, by decide⟩ →
      t.write = false ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root278] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root278_forbidden_parent (n : Nat) (c : Config)
    (hr : run root278 n blank = some c)
    (hs : readSlot c = (⟨4, by decide⟩, false)) :
    ∃ d, rawStep root278 c = some d ∧
      d.state = ⟨0, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root278 ⟨4, by decide⟩ false
    true true ⟨0, by decide⟩ true
    (by decide) root278_entry (by decide) n c hr hs

#print axioms root278_forbidden_parent

/-- Holdout #286: 1RB1RE_1LC0RA_---1LD_1LA0LF_0LB0LC_1RB0LB
Blocked immediate predecessor E/1 -> C/0;
there are 2 total input rows entering its halting state. -/
def root286 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨true, true, ⟨4, by decide⟩⟩
  | 1, false => some ⟨true, false, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, true, ⟨0, by decide⟩⟩
  | 2, false => none
  | 2, true => some ⟨true, false, ⟨3, by decide⟩⟩
  | 3, false => some ⟨true, false, ⟨0, by decide⟩⟩
  | 3, true => some ⟨false, false, ⟨5, by decide⟩⟩
  | 4, false => some ⟨false, false, ⟨1, by decide⟩⟩
  | 4, true => some ⟨false, false, ⟨2, by decide⟩⟩
  | 5, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 5, true => some ⟨false, false, ⟨1, by decide⟩⟩
  | _, _ => none

private theorem root286_entry :
    ∀ (s : Slot) (t : Move), root286 s = some t →
      t.next = ⟨4, by decide⟩ →
      t.write = true ∧ t.right = true := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root286] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root286_forbidden_parent (n : Nat) (c : Config)
    (hr : run root286 n blank = some c)
    (hs : readSlot c = (⟨4, by decide⟩, true)) :
    ∃ d, rawStep root286 c = some d ∧
      d.state = ⟨2, by decide⟩ ∧ d.tape d.head ≠ false := by
  exact forbidden_transition root286 ⟨4, by decide⟩ true
    false false ⟨2, by decide⟩ false
    (by decide) root286_entry (by decide) n c hr hs

#print axioms root286_forbidden_parent

/-- Holdout #289: 1RB0LA_0LC0RA_1LA1LD_1LC0LE_1RF0LF_0RB---
Blocked immediate predecessor E/0 -> F/1;
there are 2 total input rows entering its halting state. -/
def root289 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, false, ⟨0, by decide⟩⟩
  | 1, false => some ⟨false, false, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, true, ⟨0, by decide⟩⟩
  | 2, false => some ⟨true, false, ⟨0, by decide⟩⟩
  | 2, true => some ⟨true, false, ⟨3, by decide⟩⟩
  | 3, false => some ⟨true, false, ⟨2, by decide⟩⟩
  | 3, true => some ⟨false, false, ⟨4, by decide⟩⟩
  | 4, false => some ⟨true, true, ⟨5, by decide⟩⟩
  | 4, true => some ⟨false, false, ⟨5, by decide⟩⟩
  | 5, false => some ⟨false, true, ⟨1, by decide⟩⟩
  | 5, true => none
  | _, _ => none

private theorem root289_entry :
    ∀ (s : Slot) (t : Move), root289 s = some t →
      t.next = ⟨4, by decide⟩ →
      t.write = false ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root289] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root289_forbidden_parent (n : Nat) (c : Config)
    (hr : run root289 n blank = some c)
    (hs : readSlot c = (⟨4, by decide⟩, false)) :
    ∃ d, rawStep root289 c = some d ∧
      d.state = ⟨5, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root289 ⟨4, by decide⟩ false
    true true ⟨5, by decide⟩ true
    (by decide) root289_entry (by decide) n c hr hs

#print axioms root289_forbidden_parent

/-- Holdout #296: 1RB---_1LC0LD_0RF0LD_0LE0RA_0LC1RA_1RC1RD
Blocked immediate predecessor E/1 -> A/1;
there are 2 total input rows entering its halting state. -/
def root296 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => none
  | 1, false => some ⟨true, false, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, false, ⟨3, by decide⟩⟩
  | 2, false => some ⟨false, true, ⟨5, by decide⟩⟩
  | 2, true => some ⟨false, false, ⟨3, by decide⟩⟩
  | 3, false => some ⟨false, false, ⟨4, by decide⟩⟩
  | 3, true => some ⟨false, true, ⟨0, by decide⟩⟩
  | 4, false => some ⟨false, false, ⟨2, by decide⟩⟩
  | 4, true => some ⟨true, true, ⟨0, by decide⟩⟩
  | 5, false => some ⟨true, true, ⟨2, by decide⟩⟩
  | 5, true => some ⟨true, true, ⟨3, by decide⟩⟩
  | _, _ => none

private theorem root296_entry :
    ∀ (s : Slot) (t : Move), root296 s = some t →
      t.next = ⟨4, by decide⟩ →
      t.write = false ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root296] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root296_forbidden_parent (n : Nat) (c : Config)
    (hr : run root296 n blank = some c)
    (hs : readSlot c = (⟨4, by decide⟩, true)) :
    ∃ d, rawStep root296 c = some d ∧
      d.state = ⟨0, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root296 ⟨4, by decide⟩ true
    true true ⟨0, by decide⟩ true
    (by decide) root296_entry (by decide) n c hr hs

#print axioms root296_forbidden_parent

/-- Holdout #318: 1RB0RA_1LC0RD_---0LD_1LE1LF_1RA1LB_1RC0LD
Blocked immediate predecessor F/0 -> C/0;
there are 2 total input rows entering its halting state. -/
def root318 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, true, ⟨0, by decide⟩⟩
  | 1, false => some ⟨true, false, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, true, ⟨3, by decide⟩⟩
  | 2, false => none
  | 2, true => some ⟨false, false, ⟨3, by decide⟩⟩
  | 3, false => some ⟨true, false, ⟨4, by decide⟩⟩
  | 3, true => some ⟨true, false, ⟨5, by decide⟩⟩
  | 4, false => some ⟨true, true, ⟨0, by decide⟩⟩
  | 4, true => some ⟨true, false, ⟨1, by decide⟩⟩
  | 5, false => some ⟨true, true, ⟨2, by decide⟩⟩
  | 5, true => some ⟨false, false, ⟨3, by decide⟩⟩
  | _, _ => none

private theorem root318_entry :
    ∀ (s : Slot) (t : Move), root318 s = some t →
      t.next = ⟨5, by decide⟩ →
      t.write = true ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root318] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root318_forbidden_parent (n : Nat) (c : Config)
    (hr : run root318 n blank = some c)
    (hs : readSlot c = (⟨5, by decide⟩, false)) :
    ∃ d, rawStep root318 c = some d ∧
      d.state = ⟨2, by decide⟩ ∧ d.tape d.head ≠ false := by
  exact forbidden_transition root318 ⟨5, by decide⟩ false
    true false ⟨2, by decide⟩ true
    (by decide) root318_entry (by decide) n c hr hs

#print axioms root318_forbidden_parent

/-- Holdout #325: 1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA
Blocked immediate predecessor D/0 -> E/0;
there are 2 total input rows entering its halting state. -/
def root325 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨true, false, ⟨0, by decide⟩⟩
  | 1, false => some ⟨true, false, ⟨0, by decide⟩⟩
  | 1, true => some ⟨false, true, ⟨2, by decide⟩⟩
  | 2, false => some ⟨true, true, ⟨3, by decide⟩⟩
  | 2, true => some ⟨true, true, ⟨2, by decide⟩⟩
  | 3, false => some ⟨true, false, ⟨4, by decide⟩⟩
  | 3, true => some ⟨false, true, ⟨2, by decide⟩⟩
  | 4, false => none
  | 4, true => some ⟨false, false, ⟨5, by decide⟩⟩
  | 5, false => some ⟨true, false, ⟨4, by decide⟩⟩
  | 5, true => some ⟨false, false, ⟨0, by decide⟩⟩
  | _, _ => none

private theorem root325_entry :
    ∀ (s : Slot) (t : Move), root325 s = some t →
      t.next = ⟨3, by decide⟩ →
      t.write = true ∧ t.right = true := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root325] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root325_forbidden_parent (n : Nat) (c : Config)
    (hr : run root325 n blank = some c)
    (hs : readSlot c = (⟨3, by decide⟩, false)) :
    ∃ d, rawStep root325 c = some d ∧
      d.state = ⟨4, by decide⟩ ∧ d.tape d.head ≠ false := by
  exact forbidden_transition root325 ⟨3, by decide⟩ false
    false false ⟨4, by decide⟩ true
    (by decide) root325_entry (by decide) n c hr hs

#print axioms root325_forbidden_parent

/-- Holdout #337: 1RB0LF_1LC1RC_0RA0LD_0LE1RE_0RF0LC_1RC---
Blocked immediate predecessor A/1 -> F/1;
there are 2 total input rows entering its halting state. -/
def root337 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, false, ⟨5, by decide⟩⟩
  | 1, false => some ⟨true, false, ⟨2, by decide⟩⟩
  | 1, true => some ⟨true, true, ⟨2, by decide⟩⟩
  | 2, false => some ⟨false, true, ⟨0, by decide⟩⟩
  | 2, true => some ⟨false, false, ⟨3, by decide⟩⟩
  | 3, false => some ⟨false, false, ⟨4, by decide⟩⟩
  | 3, true => some ⟨true, true, ⟨4, by decide⟩⟩
  | 4, false => some ⟨false, true, ⟨5, by decide⟩⟩
  | 4, true => some ⟨false, false, ⟨2, by decide⟩⟩
  | 5, false => some ⟨true, true, ⟨2, by decide⟩⟩
  | 5, true => none
  | _, _ => none

private theorem root337_entry :
    ∀ (s : Slot) (t : Move), root337 s = some t →
      t.next = ⟨0, by decide⟩ →
      t.write = false ∧ t.right = true := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root337] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root337_forbidden_parent (n : Nat) (c : Config)
    (hr : run root337 n blank = some c)
    (hs : readSlot c = (⟨0, by decide⟩, true)) :
    ∃ d, rawStep root337 c = some d ∧
      d.state = ⟨5, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root337 ⟨0, by decide⟩ true
    false true ⟨5, by decide⟩ false
    (by decide) root337_entry (by decide) n c hr hs

#print axioms root337_forbidden_parent

/-- Holdout #348: 1RB0RC_0LA0RA_0LD0RA_1LE---_0LF1LB_1LA1LD
Blocked immediate predecessor C/0 -> D/1;
there are 2 total input rows entering its halting state. -/
def root348 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, true, ⟨2, by decide⟩⟩
  | 1, false => some ⟨false, false, ⟨0, by decide⟩⟩
  | 1, true => some ⟨false, true, ⟨0, by decide⟩⟩
  | 2, false => some ⟨false, false, ⟨3, by decide⟩⟩
  | 2, true => some ⟨false, true, ⟨0, by decide⟩⟩
  | 3, false => some ⟨true, false, ⟨4, by decide⟩⟩
  | 3, true => none
  | 4, false => some ⟨false, false, ⟨5, by decide⟩⟩
  | 4, true => some ⟨true, false, ⟨1, by decide⟩⟩
  | 5, false => some ⟨true, false, ⟨0, by decide⟩⟩
  | 5, true => some ⟨true, false, ⟨3, by decide⟩⟩
  | _, _ => none

private theorem root348_entry :
    ∀ (s : Slot) (t : Move), root348 s = some t →
      t.next = ⟨2, by decide⟩ →
      t.write = false ∧ t.right = true := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root348] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root348_forbidden_parent (n : Nat) (c : Config)
    (hr : run root348 n blank = some c)
    (hs : readSlot c = (⟨2, by decide⟩, false)) :
    ∃ d, rawStep root348 c = some d ∧
      d.state = ⟨3, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root348 ⟨2, by decide⟩ false
    false true ⟨3, by decide⟩ false
    (by decide) root348_entry (by decide) n c hr hs

#print axioms root348_forbidden_parent

/-- Holdout #355: 1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA
Blocked immediate predecessor F/0 -> D/1;
there are 2 total input rows entering its halting state. -/
def root355 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, false, ⟨5, by decide⟩⟩
  | 1, false => some ⟨true, true, ⟨2, by decide⟩⟩
  | 1, true => some ⟨true, true, ⟨0, by decide⟩⟩
  | 2, false => some ⟨false, true, ⟨3, by decide⟩⟩
  | 2, true => some ⟨false, true, ⟨1, by decide⟩⟩
  | 3, false => some ⟨true, false, ⟨4, by decide⟩⟩
  | 3, true => none
  | 4, false => some ⟨false, false, ⟨0, by decide⟩⟩
  | 4, true => some ⟨true, false, ⟨4, by decide⟩⟩
  | 5, false => some ⟨true, true, ⟨3, by decide⟩⟩
  | 5, true => some ⟨true, false, ⟨0, by decide⟩⟩
  | _, _ => none

private theorem root355_entry :
    ∀ (s : Slot) (t : Move), root355 s = some t →
      t.next = ⟨5, by decide⟩ →
      t.write = false ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root355] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root355_forbidden_parent (n : Nat) (c : Config)
    (hr : run root355 n blank = some c)
    (hs : readSlot c = (⟨5, by decide⟩, false)) :
    ∃ d, rawStep root355 c = some d ∧
      d.state = ⟨3, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root355 ⟨5, by decide⟩ false
    true true ⟨3, by decide⟩ true
    (by decide) root355_entry (by decide) n c hr hs

#print axioms root355_forbidden_parent

/-- Holdout #370: 1RB0RB_1LC0LF_1RD0LB_1RE1RC_0RA---_1LA1RE
Blocked immediate predecessor F/1 -> E/1;
there are 2 total input rows entering its halting state. -/
def root370 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, true, ⟨1, by decide⟩⟩
  | 1, false => some ⟨true, false, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, false, ⟨5, by decide⟩⟩
  | 2, false => some ⟨true, true, ⟨3, by decide⟩⟩
  | 2, true => some ⟨false, false, ⟨1, by decide⟩⟩
  | 3, false => some ⟨true, true, ⟨4, by decide⟩⟩
  | 3, true => some ⟨true, true, ⟨2, by decide⟩⟩
  | 4, false => some ⟨false, true, ⟨0, by decide⟩⟩
  | 4, true => none
  | 5, false => some ⟨true, false, ⟨0, by decide⟩⟩
  | 5, true => some ⟨true, true, ⟨4, by decide⟩⟩
  | _, _ => none

private theorem root370_entry :
    ∀ (s : Slot) (t : Move), root370 s = some t →
      t.next = ⟨5, by decide⟩ →
      t.write = false ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root370] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root370_forbidden_parent (n : Nat) (c : Config)
    (hr : run root370 n blank = some c)
    (hs : readSlot c = (⟨5, by decide⟩, true)) :
    ∃ d, rawStep root370 c = some d ∧
      d.state = ⟨4, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root370 ⟨5, by decide⟩ true
    true true ⟨4, by decide⟩ true
    (by decide) root370_entry (by decide) n c hr hs

#print axioms root370_forbidden_parent

/-- Holdout #388: 1RB0RE_1LC0RA_0LD0LB_1RE0LB_1RF---_0RB0RC
Blocked immediate predecessor D/0 -> E/1;
there are 2 total input rows entering its halting state. -/
def root388 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, true, ⟨4, by decide⟩⟩
  | 1, false => some ⟨true, false, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, true, ⟨0, by decide⟩⟩
  | 2, false => some ⟨false, false, ⟨3, by decide⟩⟩
  | 2, true => some ⟨false, false, ⟨1, by decide⟩⟩
  | 3, false => some ⟨true, true, ⟨4, by decide⟩⟩
  | 3, true => some ⟨false, false, ⟨1, by decide⟩⟩
  | 4, false => some ⟨true, true, ⟨5, by decide⟩⟩
  | 4, true => none
  | 5, false => some ⟨false, true, ⟨1, by decide⟩⟩
  | 5, true => some ⟨false, true, ⟨2, by decide⟩⟩
  | _, _ => none

private theorem root388_entry :
    ∀ (s : Slot) (t : Move), root388 s = some t →
      t.next = ⟨3, by decide⟩ →
      t.write = false ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root388] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root388_forbidden_parent (n : Nat) (c : Config)
    (hr : run root388 n blank = some c)
    (hs : readSlot c = (⟨3, by decide⟩, false)) :
    ∃ d, rawStep root388 c = some d ∧
      d.state = ⟨4, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root388 ⟨3, by decide⟩ false
    true true ⟨4, by decide⟩ true
    (by decide) root388_entry (by decide) n c hr hs

#print axioms root388_forbidden_parent

/-- Holdout #395: 1RB1LA_1RC1RD_0LA0LD_1RE1LC_0RF0LF_---0RA
Blocked immediate predecessor E/1 -> F/0;
there are 2 total input rows entering its halting state. -/
def root395 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨true, false, ⟨0, by decide⟩⟩
  | 1, false => some ⟨true, true, ⟨2, by decide⟩⟩
  | 1, true => some ⟨true, true, ⟨3, by decide⟩⟩
  | 2, false => some ⟨false, false, ⟨0, by decide⟩⟩
  | 2, true => some ⟨false, false, ⟨3, by decide⟩⟩
  | 3, false => some ⟨true, true, ⟨4, by decide⟩⟩
  | 3, true => some ⟨true, false, ⟨2, by decide⟩⟩
  | 4, false => some ⟨false, true, ⟨5, by decide⟩⟩
  | 4, true => some ⟨false, false, ⟨5, by decide⟩⟩
  | 5, false => none
  | 5, true => some ⟨false, true, ⟨0, by decide⟩⟩
  | _, _ => none

private theorem root395_entry :
    ∀ (s : Slot) (t : Move), root395 s = some t →
      t.next = ⟨4, by decide⟩ →
      t.write = true ∧ t.right = true := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root395] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root395_forbidden_parent (n : Nat) (c : Config)
    (hr : run root395 n blank = some c)
    (hs : readSlot c = (⟨4, by decide⟩, true)) :
    ∃ d, rawStep root395 c = some d ∧
      d.state = ⟨5, by decide⟩ ∧ d.tape d.head ≠ false := by
  exact forbidden_transition root395 ⟨4, by decide⟩ true
    false false ⟨5, by decide⟩ false
    (by decide) root395_entry (by decide) n c hr hs

#print axioms root395_forbidden_parent

/-- Holdout #398: 1RB0LC_1RC0RA_1RD0RF_0LE---_1LB1LA_1LD1RA
Blocked immediate predecessor F/0 -> D/1;
there are 2 total input rows entering its halting state. -/
def root398 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, false, ⟨2, by decide⟩⟩
  | 1, false => some ⟨true, true, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, true, ⟨0, by decide⟩⟩
  | 2, false => some ⟨true, true, ⟨3, by decide⟩⟩
  | 2, true => some ⟨false, true, ⟨5, by decide⟩⟩
  | 3, false => some ⟨false, false, ⟨4, by decide⟩⟩
  | 3, true => none
  | 4, false => some ⟨true, false, ⟨1, by decide⟩⟩
  | 4, true => some ⟨true, false, ⟨0, by decide⟩⟩
  | 5, false => some ⟨true, false, ⟨3, by decide⟩⟩
  | 5, true => some ⟨true, true, ⟨0, by decide⟩⟩
  | _, _ => none

private theorem root398_entry :
    ∀ (s : Slot) (t : Move), root398 s = some t →
      t.next = ⟨5, by decide⟩ →
      t.write = false ∧ t.right = true := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root398] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root398_forbidden_parent (n : Nat) (c : Config)
    (hr : run root398 n blank = some c)
    (hs : readSlot c = (⟨5, by decide⟩, false)) :
    ∃ d, rawStep root398 c = some d ∧
      d.state = ⟨3, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root398 ⟨5, by decide⟩ false
    false true ⟨3, by decide⟩ true
    (by decide) root398_entry (by decide) n c hr hs

#print axioms root398_forbidden_parent

/-- Holdout #400: 1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD
Blocked immediate predecessor A/0 -> B/1;
there are 2 total input rows entering its halting state. -/
def root400 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, false, ⟨4, by decide⟩⟩
  | 1, false => some ⟨true, true, ⟨2, by decide⟩⟩
  | 1, true => none
  | 2, false => some ⟨false, true, ⟨3, by decide⟩⟩
  | 2, true => some ⟨false, true, ⟨4, by decide⟩⟩
  | 3, false => some ⟨true, false, ⟨4, by decide⟩⟩
  | 3, true => some ⟨false, true, ⟨1, by decide⟩⟩
  | 4, false => some ⟨false, false, ⟨0, by decide⟩⟩
  | 4, true => some ⟨false, false, ⟨5, by decide⟩⟩
  | 5, false => some ⟨false, true, ⟨2, by decide⟩⟩
  | 5, true => some ⟨false, false, ⟨3, by decide⟩⟩
  | _, _ => none

private theorem root400_entry :
    ∀ (s : Slot) (t : Move), root400 s = some t →
      t.next = ⟨0, by decide⟩ →
      t.write = false ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root400] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root400_forbidden_parent (n : Nat) (c : Config)
    (hr : run root400 n blank = some c)
    (hs : readSlot c = (⟨0, by decide⟩, false)) :
    ∃ d, rawStep root400 c = some d ∧
      d.state = ⟨1, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root400 ⟨0, by decide⟩ false
    true true ⟨1, by decide⟩ true
    (by decide) root400_entry (by decide) n c hr hs

#print axioms root400_forbidden_parent

/-- Holdout #408: 1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---
Blocked immediate predecessor E/1 -> F/1;
there are 2 total input rows entering its halting state. -/
def root408 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, false, ⟨4, by decide⟩⟩
  | 1, false => some ⟨false, true, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, true, ⟨0, by decide⟩⟩
  | 2, false => some ⟨true, true, ⟨3, by decide⟩⟩
  | 2, true => some ⟨true, true, ⟨5, by decide⟩⟩
  | 3, false => some ⟨true, false, ⟨0, by decide⟩⟩
  | 3, true => some ⟨false, false, ⟨3, by decide⟩⟩
  | 4, false => some ⟨true, false, ⟨3, by decide⟩⟩
  | 4, true => some ⟨false, true, ⟨5, by decide⟩⟩
  | 5, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 5, true => none
  | _, _ => none

private theorem root408_entry :
    ∀ (s : Slot) (t : Move), root408 s = some t →
      t.next = ⟨4, by decide⟩ →
      t.write = false ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root408] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root408_forbidden_parent (n : Nat) (c : Config)
    (hr : run root408 n blank = some c)
    (hs : readSlot c = (⟨4, by decide⟩, true)) :
    ∃ d, rawStep root408 c = some d ∧
      d.state = ⟨5, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root408 ⟨4, by decide⟩ true
    true true ⟨5, by decide⟩ false
    (by decide) root408_entry (by decide) n c hr hs

#print axioms root408_forbidden_parent

/-- Holdout #421: 1RB0RD_0LC0LF_1RD1LB_0RE---_1RA0LC_0LA1LF
Blocked immediate predecessor C/0 -> D/1;
there are 2 total input rows entering its halting state. -/
def root421 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, true, ⟨3, by decide⟩⟩
  | 1, false => some ⟨false, false, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, false, ⟨5, by decide⟩⟩
  | 2, false => some ⟨true, true, ⟨3, by decide⟩⟩
  | 2, true => some ⟨true, false, ⟨1, by decide⟩⟩
  | 3, false => some ⟨false, true, ⟨4, by decide⟩⟩
  | 3, true => none
  | 4, false => some ⟨true, true, ⟨0, by decide⟩⟩
  | 4, true => some ⟨false, false, ⟨2, by decide⟩⟩
  | 5, false => some ⟨false, false, ⟨0, by decide⟩⟩
  | 5, true => some ⟨true, false, ⟨5, by decide⟩⟩
  | _, _ => none

private theorem root421_entry :
    ∀ (s : Slot) (t : Move), root421 s = some t →
      t.next = ⟨2, by decide⟩ →
      t.write = false ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root421] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root421_forbidden_parent (n : Nat) (c : Config)
    (hr : run root421 n blank = some c)
    (hs : readSlot c = (⟨2, by decide⟩, false)) :
    ∃ d, rawStep root421 c = some d ∧
      d.state = ⟨3, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root421 ⟨2, by decide⟩ false
    true true ⟨3, by decide⟩ true
    (by decide) root421_entry (by decide) n c hr hs

#print axioms root421_forbidden_parent

/-- Holdout #456: 1RB1LE_0RC1RA_0LD0RB_1LA1LF_0LC1RF_---0LA
Blocked immediate predecessor E/1 -> F/0;
there are 2 total input rows entering its halting state. -/
def root456 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨true, false, ⟨4, by decide⟩⟩
  | 1, false => some ⟨false, true, ⟨2, by decide⟩⟩
  | 1, true => some ⟨true, true, ⟨0, by decide⟩⟩
  | 2, false => some ⟨false, false, ⟨3, by decide⟩⟩
  | 2, true => some ⟨false, true, ⟨1, by decide⟩⟩
  | 3, false => some ⟨true, false, ⟨0, by decide⟩⟩
  | 3, true => some ⟨true, false, ⟨5, by decide⟩⟩
  | 4, false => some ⟨false, false, ⟨2, by decide⟩⟩
  | 4, true => some ⟨true, true, ⟨5, by decide⟩⟩
  | 5, false => none
  | 5, true => some ⟨false, false, ⟨0, by decide⟩⟩
  | _, _ => none

private theorem root456_entry :
    ∀ (s : Slot) (t : Move), root456 s = some t →
      t.next = ⟨4, by decide⟩ →
      t.write = true ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root456] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root456_forbidden_parent (n : Nat) (c : Config)
    (hr : run root456 n blank = some c)
    (hs : readSlot c = (⟨4, by decide⟩, true)) :
    ∃ d, rawStep root456 c = some d ∧
      d.state = ⟨5, by decide⟩ ∧ d.tape d.head ≠ false := by
  exact forbidden_transition root456 ⟨4, by decide⟩ true
    true false ⟨5, by decide⟩ true
    (by decide) root456_entry (by decide) n c hr hs

#print axioms root456_forbidden_parent

/-- Holdout #463: 1RB1LF_0RC---_1RD1RF_1LE0LF_1LB0LA_1LD0RE
Blocked immediate predecessor A/0 -> B/1;
there are 2 total input rows entering its halting state. -/
def root463 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨true, false, ⟨5, by decide⟩⟩
  | 1, false => some ⟨false, true, ⟨2, by decide⟩⟩
  | 1, true => none
  | 2, false => some ⟨true, true, ⟨3, by decide⟩⟩
  | 2, true => some ⟨true, true, ⟨5, by decide⟩⟩
  | 3, false => some ⟨true, false, ⟨4, by decide⟩⟩
  | 3, true => some ⟨false, false, ⟨5, by decide⟩⟩
  | 4, false => some ⟨true, false, ⟨1, by decide⟩⟩
  | 4, true => some ⟨false, false, ⟨0, by decide⟩⟩
  | 5, false => some ⟨true, false, ⟨3, by decide⟩⟩
  | 5, true => some ⟨false, true, ⟨4, by decide⟩⟩
  | _, _ => none

private theorem root463_entry :
    ∀ (s : Slot) (t : Move), root463 s = some t →
      t.next = ⟨0, by decide⟩ →
      t.write = false ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root463] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root463_forbidden_parent (n : Nat) (c : Config)
    (hr : run root463 n blank = some c)
    (hs : readSlot c = (⟨0, by decide⟩, false)) :
    ∃ d, rawStep root463 c = some d ∧
      d.state = ⟨1, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root463 ⟨0, by decide⟩ false
    true true ⟨1, by decide⟩ true
    (by decide) root463_entry (by decide) n c hr hs

#print axioms root463_forbidden_parent

/-- Holdout #468: 1RB0LD_1RC---_0RD0RE_1LE0RF_0LA0LD_1RD0RB
Blocked immediate predecessor A/0 -> B/1;
there are 2 total input rows entering its halting state. -/
def root468 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, false, ⟨3, by decide⟩⟩
  | 1, false => some ⟨true, true, ⟨2, by decide⟩⟩
  | 1, true => none
  | 2, false => some ⟨false, true, ⟨3, by decide⟩⟩
  | 2, true => some ⟨false, true, ⟨4, by decide⟩⟩
  | 3, false => some ⟨true, false, ⟨4, by decide⟩⟩
  | 3, true => some ⟨false, true, ⟨5, by decide⟩⟩
  | 4, false => some ⟨false, false, ⟨0, by decide⟩⟩
  | 4, true => some ⟨false, false, ⟨3, by decide⟩⟩
  | 5, false => some ⟨true, true, ⟨3, by decide⟩⟩
  | 5, true => some ⟨false, true, ⟨1, by decide⟩⟩
  | _, _ => none

private theorem root468_entry :
    ∀ (s : Slot) (t : Move), root468 s = some t →
      t.next = ⟨0, by decide⟩ →
      t.write = false ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root468] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root468_forbidden_parent (n : Nat) (c : Config)
    (hr : run root468 n blank = some c)
    (hs : readSlot c = (⟨0, by decide⟩, false)) :
    ∃ d, rawStep root468 c = some d ∧
      d.state = ⟨1, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root468 ⟨0, by decide⟩ false
    true true ⟨1, by decide⟩ true
    (by decide) root468_entry (by decide) n c hr hs

#print axioms root468_forbidden_parent

/-- Holdout #483: 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD
Blocked immediate predecessor F/1 -> D/1;
there are 2 total input rows entering its halting state. -/
def root483 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, false, ⟨2, by decide⟩⟩
  | 1, false => some ⟨true, true, ⟨2, by decide⟩⟩
  | 1, true => some ⟨true, true, ⟨0, by decide⟩⟩
  | 2, false => some ⟨true, true, ⟨3, by decide⟩⟩
  | 2, true => some ⟨false, true, ⟨5, by decide⟩⟩
  | 3, false => some ⟨false, false, ⟨4, by decide⟩⟩
  | 3, true => none
  | 4, false => some ⟨true, false, ⟨0, by decide⟩⟩
  | 4, true => some ⟨true, false, ⟨4, by decide⟩⟩
  | 5, false => some ⟨false, true, ⟨0, by decide⟩⟩
  | 5, true => some ⟨true, false, ⟨3, by decide⟩⟩
  | _, _ => none

private theorem root483_entry :
    ∀ (s : Slot) (t : Move), root483 s = some t →
      t.next = ⟨5, by decide⟩ →
      t.write = false ∧ t.right = true := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root483] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root483_forbidden_parent (n : Nat) (c : Config)
    (hr : run root483 n blank = some c)
    (hs : readSlot c = (⟨5, by decide⟩, true)) :
    ∃ d, rawStep root483 c = some d ∧
      d.state = ⟨3, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root483 ⟨5, by decide⟩ true
    false true ⟨3, by decide⟩ true
    (by decide) root483_entry (by decide) n c hr hs

#print axioms root483_forbidden_parent

/-- Holdout #488: 1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE
Blocked immediate predecessor F/0 -> D/1;
there are 2 total input rows entering its halting state. -/
def root488 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, true, ⟨4, by decide⟩⟩
  | 1, false => some ⟨true, false, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, true, ⟨0, by decide⟩⟩
  | 2, false => some ⟨true, false, ⟨0, by decide⟩⟩
  | 2, true => some ⟨true, false, ⟨3, by decide⟩⟩
  | 3, false => some ⟨true, false, ⟨0, by decide⟩⟩
  | 3, true => none
  | 4, false => some ⟨false, true, ⟨5, by decide⟩⟩
  | 4, true => some ⟨false, false, ⟨1, by decide⟩⟩
  | 5, false => some ⟨false, false, ⟨3, by decide⟩⟩
  | 5, true => some ⟨true, true, ⟨4, by decide⟩⟩
  | _, _ => none

private theorem root488_entry :
    ∀ (s : Slot) (t : Move), root488 s = some t →
      t.next = ⟨5, by decide⟩ →
      t.write = false ∧ t.right = true := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root488] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root488_forbidden_parent (n : Nat) (c : Config)
    (hr : run root488 n blank = some c)
    (hs : readSlot c = (⟨5, by decide⟩, false)) :
    ∃ d, rawStep root488 c = some d ∧
      d.state = ⟨3, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root488 ⟨5, by decide⟩ false
    false true ⟨3, by decide⟩ false
    (by decide) root488_entry (by decide) n c hr hs

#print axioms root488_forbidden_parent

/-- Holdout #499: 1RB0LF_1RC0RB_0RD0RA_1RE1LE_1RF---_1LA1LF
Blocked immediate predecessor D/1 -> E/1;
there are 2 total input rows entering its halting state. -/
def root499 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, false, ⟨5, by decide⟩⟩
  | 1, false => some ⟨true, true, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, true, ⟨1, by decide⟩⟩
  | 2, false => some ⟨false, true, ⟨3, by decide⟩⟩
  | 2, true => some ⟨false, true, ⟨0, by decide⟩⟩
  | 3, false => some ⟨true, true, ⟨4, by decide⟩⟩
  | 3, true => some ⟨true, false, ⟨4, by decide⟩⟩
  | 4, false => some ⟨true, true, ⟨5, by decide⟩⟩
  | 4, true => none
  | 5, false => some ⟨true, false, ⟨0, by decide⟩⟩
  | 5, true => some ⟨true, false, ⟨5, by decide⟩⟩
  | _, _ => none

private theorem root499_entry :
    ∀ (s : Slot) (t : Move), root499 s = some t →
      t.next = ⟨3, by decide⟩ →
      t.write = false ∧ t.right = true := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root499] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root499_forbidden_parent (n : Nat) (c : Config)
    (hr : run root499 n blank = some c)
    (hs : readSlot c = (⟨3, by decide⟩, true)) :
    ∃ d, rawStep root499 c = some d ∧
      d.state = ⟨4, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root499 ⟨3, by decide⟩ true
    false true ⟨4, by decide⟩ true
    (by decide) root499_entry (by decide) n c hr hs

#print axioms root499_forbidden_parent

/-- Holdout #502: 1RB---_0LC0RB_1RA1LD_0RD1LE_1LF0LA_1LB0LE
Blocked immediate predecessor C/0 -> A/1;
there are 2 total input rows entering its halting state. -/
def root502 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => none
  | 1, false => some ⟨false, false, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, true, ⟨1, by decide⟩⟩
  | 2, false => some ⟨true, true, ⟨0, by decide⟩⟩
  | 2, true => some ⟨true, false, ⟨3, by decide⟩⟩
  | 3, false => some ⟨false, true, ⟨3, by decide⟩⟩
  | 3, true => some ⟨true, false, ⟨4, by decide⟩⟩
  | 4, false => some ⟨true, false, ⟨5, by decide⟩⟩
  | 4, true => some ⟨false, false, ⟨0, by decide⟩⟩
  | 5, false => some ⟨true, false, ⟨1, by decide⟩⟩
  | 5, true => some ⟨false, false, ⟨4, by decide⟩⟩
  | _, _ => none

private theorem root502_entry :
    ∀ (s : Slot) (t : Move), root502 s = some t →
      t.next = ⟨2, by decide⟩ →
      t.write = false ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root502] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root502_forbidden_parent (n : Nat) (c : Config)
    (hr : run root502 n blank = some c)
    (hs : readSlot c = (⟨2, by decide⟩, false)) :
    ∃ d, rawStep root502 c = some d ∧
      d.state = ⟨0, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root502 ⟨2, by decide⟩ false
    true true ⟨0, by decide⟩ true
    (by decide) root502_entry (by decide) n c hr hs

#print axioms root502_forbidden_parent

/-- Holdout #505: 1RB1RF_1RC0RB_0RD1LF_1LE1RE_1LA---_1RA0LC
Blocked immediate predecessor D/0 -> E/1;
there are 2 total input rows entering its halting state. -/
def root505 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨true, true, ⟨5, by decide⟩⟩
  | 1, false => some ⟨true, true, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, true, ⟨1, by decide⟩⟩
  | 2, false => some ⟨false, true, ⟨3, by decide⟩⟩
  | 2, true => some ⟨true, false, ⟨5, by decide⟩⟩
  | 3, false => some ⟨true, false, ⟨4, by decide⟩⟩
  | 3, true => some ⟨true, true, ⟨4, by decide⟩⟩
  | 4, false => some ⟨true, false, ⟨0, by decide⟩⟩
  | 4, true => none
  | 5, false => some ⟨true, true, ⟨0, by decide⟩⟩
  | 5, true => some ⟨false, false, ⟨2, by decide⟩⟩
  | _, _ => none

private theorem root505_entry :
    ∀ (s : Slot) (t : Move), root505 s = some t →
      t.next = ⟨3, by decide⟩ →
      t.write = false ∧ t.right = true := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root505] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root505_forbidden_parent (n : Nat) (c : Config)
    (hr : run root505 n blank = some c)
    (hs : readSlot c = (⟨3, by decide⟩, false)) :
    ∃ d, rawStep root505 c = some d ∧
      d.state = ⟨4, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root505 ⟨3, by decide⟩ false
    false true ⟨4, by decide⟩ true
    (by decide) root505_entry (by decide) n c hr hs

#print axioms root505_forbidden_parent

/-- Holdout #509: 1RB0LF_1RC0RB_1LD0RA_0LE0LC_1LB1LF_1LD---
Blocked immediate predecessor A/1 -> F/1;
there are 2 total input rows entering its halting state. -/
def root509 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, false, ⟨5, by decide⟩⟩
  | 1, false => some ⟨true, true, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, true, ⟨1, by decide⟩⟩
  | 2, false => some ⟨true, false, ⟨3, by decide⟩⟩
  | 2, true => some ⟨false, true, ⟨0, by decide⟩⟩
  | 3, false => some ⟨false, false, ⟨4, by decide⟩⟩
  | 3, true => some ⟨false, false, ⟨2, by decide⟩⟩
  | 4, false => some ⟨true, false, ⟨1, by decide⟩⟩
  | 4, true => some ⟨true, false, ⟨5, by decide⟩⟩
  | 5, false => some ⟨true, false, ⟨3, by decide⟩⟩
  | 5, true => none
  | _, _ => none

private theorem root509_entry :
    ∀ (s : Slot) (t : Move), root509 s = some t →
      t.next = ⟨0, by decide⟩ →
      t.write = false ∧ t.right = true := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root509] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root509_forbidden_parent (n : Nat) (c : Config)
    (hr : run root509 n blank = some c)
    (hs : readSlot c = (⟨0, by decide⟩, true)) :
    ∃ d, rawStep root509 c = some d ∧
      d.state = ⟨5, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root509 ⟨0, by decide⟩ true
    false true ⟨5, by decide⟩ false
    (by decide) root509_entry (by decide) n c hr hs

#print axioms root509_forbidden_parent

/-- Holdout #546: 1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RA---_1RB1LF
Blocked immediate predecessor D/0 -> E/1;
there are 2 total input rows entering its halting state. -/
def root546 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨true, true, ⟨0, by decide⟩⟩
  | 1, false => some ⟨true, false, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, true, ⟨2, by decide⟩⟩
  | 2, false => some ⟨true, true, ⟨4, by decide⟩⟩
  | 2, true => some ⟨false, false, ⟨3, by decide⟩⟩
  | 3, false => some ⟨false, true, ⟨4, by decide⟩⟩
  | 3, true => some ⟨false, false, ⟨5, by decide⟩⟩
  | 4, false => some ⟨true, true, ⟨0, by decide⟩⟩
  | 4, true => none
  | 5, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 5, true => some ⟨true, false, ⟨5, by decide⟩⟩
  | _, _ => none

private theorem root546_entry :
    ∀ (s : Slot) (t : Move), root546 s = some t →
      t.next = ⟨3, by decide⟩ →
      t.write = false ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root546] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root546_forbidden_parent (n : Nat) (c : Config)
    (hr : run root546 n blank = some c)
    (hs : readSlot c = (⟨3, by decide⟩, false)) :
    ∃ d, rawStep root546 c = some d ∧
      d.state = ⟨4, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root546 ⟨3, by decide⟩ false
    true true ⟨4, by decide⟩ false
    (by decide) root546_entry (by decide) n c hr hs

#print axioms root546_forbidden_parent

/-- Holdout #555: 1RB---_1RC1RB_1LD0RB_1LE0LD_0LF0LC_1LA1RA
Blocked immediate predecessor F/1 -> A/1;
there are 2 total input rows entering its halting state. -/
def root555 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => none
  | 1, false => some ⟨true, true, ⟨2, by decide⟩⟩
  | 1, true => some ⟨true, true, ⟨1, by decide⟩⟩
  | 2, false => some ⟨true, false, ⟨3, by decide⟩⟩
  | 2, true => some ⟨false, true, ⟨1, by decide⟩⟩
  | 3, false => some ⟨true, false, ⟨4, by decide⟩⟩
  | 3, true => some ⟨false, false, ⟨3, by decide⟩⟩
  | 4, false => some ⟨false, false, ⟨5, by decide⟩⟩
  | 4, true => some ⟨false, false, ⟨2, by decide⟩⟩
  | 5, false => some ⟨true, false, ⟨0, by decide⟩⟩
  | 5, true => some ⟨true, true, ⟨0, by decide⟩⟩
  | _, _ => none

private theorem root555_entry :
    ∀ (s : Slot) (t : Move), root555 s = some t →
      t.next = ⟨5, by decide⟩ →
      t.write = false ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root555] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root555_forbidden_parent (n : Nat) (c : Config)
    (hr : run root555 n blank = some c)
    (hs : readSlot c = (⟨5, by decide⟩, true)) :
    ∃ d, rawStep root555 c = some d ∧
      d.state = ⟨0, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root555 ⟨5, by decide⟩ true
    true true ⟨0, by decide⟩ true
    (by decide) root555_entry (by decide) n c hr hs

#print axioms root555_forbidden_parent

/-- Holdout #561: 1RB1LC_1LA---_1LD0LA_1RE0LE_0RF1RE_1LB1RD
Blocked immediate predecessor F/0 -> B/1;
there are 2 total input rows entering its halting state. -/
def root561 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨true, false, ⟨2, by decide⟩⟩
  | 1, false => some ⟨true, false, ⟨0, by decide⟩⟩
  | 1, true => none
  | 2, false => some ⟨true, false, ⟨3, by decide⟩⟩
  | 2, true => some ⟨false, false, ⟨0, by decide⟩⟩
  | 3, false => some ⟨true, true, ⟨4, by decide⟩⟩
  | 3, true => some ⟨false, false, ⟨4, by decide⟩⟩
  | 4, false => some ⟨false, true, ⟨5, by decide⟩⟩
  | 4, true => some ⟨true, true, ⟨4, by decide⟩⟩
  | 5, false => some ⟨true, false, ⟨1, by decide⟩⟩
  | 5, true => some ⟨true, true, ⟨3, by decide⟩⟩
  | _, _ => none

private theorem root561_entry :
    ∀ (s : Slot) (t : Move), root561 s = some t →
      t.next = ⟨5, by decide⟩ →
      t.write = false ∧ t.right = true := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root561] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root561_forbidden_parent (n : Nat) (c : Config)
    (hr : run root561 n blank = some c)
    (hs : readSlot c = (⟨5, by decide⟩, false)) :
    ∃ d, rawStep root561 c = some d ∧
      d.state = ⟨1, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root561 ⟨5, by decide⟩ false
    false true ⟨1, by decide⟩ true
    (by decide) root561_entry (by decide) n c hr hs

#print axioms root561_forbidden_parent

/-- Holdout #575: 1RB1RE_1RC0LD_1LB---_1RA1LD_1RA0RF_1RE0LC
Blocked immediate predecessor F/1 -> C/1;
there are 2 total input rows entering its halting state. -/
def root575 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨true, true, ⟨4, by decide⟩⟩
  | 1, false => some ⟨true, true, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, false, ⟨3, by decide⟩⟩
  | 2, false => some ⟨true, false, ⟨1, by decide⟩⟩
  | 2, true => none
  | 3, false => some ⟨true, true, ⟨0, by decide⟩⟩
  | 3, true => some ⟨true, false, ⟨3, by decide⟩⟩
  | 4, false => some ⟨true, true, ⟨0, by decide⟩⟩
  | 4, true => some ⟨false, true, ⟨5, by decide⟩⟩
  | 5, false => some ⟨true, true, ⟨4, by decide⟩⟩
  | 5, true => some ⟨false, false, ⟨2, by decide⟩⟩
  | _, _ => none

private theorem root575_entry :
    ∀ (s : Slot) (t : Move), root575 s = some t →
      t.next = ⟨5, by decide⟩ →
      t.write = false ∧ t.right = true := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root575] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root575_forbidden_parent (n : Nat) (c : Config)
    (hr : run root575 n blank = some c)
    (hs : readSlot c = (⟨5, by decide⟩, true)) :
    ∃ d, rawStep root575 c = some d ∧
      d.state = ⟨2, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root575 ⟨5, by decide⟩ true
    false true ⟨2, by decide⟩ false
    (by decide) root575_entry (by decide) n c hr hs

#print axioms root575_forbidden_parent

/-- Holdout #579: 1RB0LD_1LC0RE_---1LD_1LE1LA_1RA0LF_1LC1RE
Blocked immediate predecessor B/0 -> C/0;
there are 2 total input rows entering its halting state. -/
def root579 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, false, ⟨3, by decide⟩⟩
  | 1, false => some ⟨true, false, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, true, ⟨4, by decide⟩⟩
  | 2, false => none
  | 2, true => some ⟨true, false, ⟨3, by decide⟩⟩
  | 3, false => some ⟨true, false, ⟨4, by decide⟩⟩
  | 3, true => some ⟨true, false, ⟨0, by decide⟩⟩
  | 4, false => some ⟨true, true, ⟨0, by decide⟩⟩
  | 4, true => some ⟨false, false, ⟨5, by decide⟩⟩
  | 5, false => some ⟨true, false, ⟨2, by decide⟩⟩
  | 5, true => some ⟨true, true, ⟨4, by decide⟩⟩
  | _, _ => none

private theorem root579_entry :
    ∀ (s : Slot) (t : Move), root579 s = some t →
      t.next = ⟨1, by decide⟩ →
      t.write = true ∧ t.right = true := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root579] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root579_forbidden_parent (n : Nat) (c : Config)
    (hr : run root579 n blank = some c)
    (hs : readSlot c = (⟨1, by decide⟩, false)) :
    ∃ d, rawStep root579 c = some d ∧
      d.state = ⟨2, by decide⟩ ∧ d.tape d.head ≠ false := by
  exact forbidden_transition root579 ⟨1, by decide⟩ false
    false false ⟨2, by decide⟩ true
    (by decide) root579_entry (by decide) n c hr hs

#print axioms root579_forbidden_parent

/-- Holdout #595: 1RB0RB_1LC1RA_0LE1LD_0RE1LF_---1LA_1LD0LC
Blocked immediate predecessor D/0 -> E/0;
there are 2 total input rows entering its halting state. -/
def root595 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, true, ⟨1, by decide⟩⟩
  | 1, false => some ⟨true, false, ⟨2, by decide⟩⟩
  | 1, true => some ⟨true, true, ⟨0, by decide⟩⟩
  | 2, false => some ⟨false, false, ⟨4, by decide⟩⟩
  | 2, true => some ⟨true, false, ⟨3, by decide⟩⟩
  | 3, false => some ⟨false, true, ⟨4, by decide⟩⟩
  | 3, true => some ⟨true, false, ⟨5, by decide⟩⟩
  | 4, false => none
  | 4, true => some ⟨true, false, ⟨0, by decide⟩⟩
  | 5, false => some ⟨true, false, ⟨3, by decide⟩⟩
  | 5, true => some ⟨false, false, ⟨2, by decide⟩⟩
  | _, _ => none

private theorem root595_entry :
    ∀ (s : Slot) (t : Move), root595 s = some t →
      t.next = ⟨3, by decide⟩ →
      t.write = true ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root595] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root595_forbidden_parent (n : Nat) (c : Config)
    (hr : run root595 n blank = some c)
    (hs : readSlot c = (⟨3, by decide⟩, false)) :
    ∃ d, rawStep root595 c = some d ∧
      d.state = ⟨4, by decide⟩ ∧ d.tape d.head ≠ false := by
  exact forbidden_transition root595 ⟨3, by decide⟩ false
    true false ⟨4, by decide⟩ false
    (by decide) root595_entry (by decide) n c hr hs

#print axioms root595_forbidden_parent

/-- Holdout #599: 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE1LC
Blocked immediate predecessor F/1 -> C/1;
there are 2 total input rows entering its halting state. -/
def root599 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨true, true, ⟨4, by decide⟩⟩
  | 1, false => some ⟨true, true, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, true, ⟨5, by decide⟩⟩
  | 2, false => some ⟨false, false, ⟨3, by decide⟩⟩
  | 2, true => none
  | 3, false => some ⟨true, false, ⟨4, by decide⟩⟩
  | 3, true => some ⟨true, false, ⟨3, by decide⟩⟩
  | 4, false => some ⟨true, true, ⟨0, by decide⟩⟩
  | 4, true => some ⟨false, false, ⟨1, by decide⟩⟩
  | 5, false => some ⟨false, true, ⟨4, by decide⟩⟩
  | 5, true => some ⟨true, false, ⟨2, by decide⟩⟩
  | _, _ => none

private theorem root599_entry :
    ∀ (s : Slot) (t : Move), root599 s = some t →
      t.next = ⟨5, by decide⟩ →
      t.write = false ∧ t.right = true := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root599] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root599_forbidden_parent (n : Nat) (c : Config)
    (hr : run root599 n blank = some c)
    (hs : readSlot c = (⟨5, by decide⟩, true)) :
    ∃ d, rawStep root599 c = some d ∧
      d.state = ⟨2, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root599 ⟨5, by decide⟩ true
    false true ⟨2, by decide⟩ true
    (by decide) root599_entry (by decide) n c hr hs

#print axioms root599_forbidden_parent

/-- Holdout #613: 1RB0LD_0RC0RF_1LD0RB_1LE---_0LA0LB_0LE0RA
Blocked immediate predecessor C/0 -> D/1;
there are 2 total input rows entering its halting state. -/
def root613 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, false, ⟨3, by decide⟩⟩
  | 1, false => some ⟨false, true, ⟨2, by decide⟩⟩
  | 1, true => some ⟨false, true, ⟨5, by decide⟩⟩
  | 2, false => some ⟨true, false, ⟨3, by decide⟩⟩
  | 2, true => some ⟨false, true, ⟨1, by decide⟩⟩
  | 3, false => some ⟨true, false, ⟨4, by decide⟩⟩
  | 3, true => none
  | 4, false => some ⟨false, false, ⟨0, by decide⟩⟩
  | 4, true => some ⟨false, false, ⟨1, by decide⟩⟩
  | 5, false => some ⟨false, false, ⟨4, by decide⟩⟩
  | 5, true => some ⟨false, true, ⟨0, by decide⟩⟩
  | _, _ => none

private theorem root613_entry :
    ∀ (s : Slot) (t : Move), root613 s = some t →
      t.next = ⟨2, by decide⟩ →
      t.write = false ∧ t.right = true := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root613] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root613_forbidden_parent (n : Nat) (c : Config)
    (hr : run root613 n blank = some c)
    (hs : readSlot c = (⟨2, by decide⟩, false)) :
    ∃ d, rawStep root613 c = some d ∧
      d.state = ⟨3, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root613 ⟨2, by decide⟩ false
    false true ⟨3, by decide⟩ true
    (by decide) root613_entry (by decide) n c hr hs

#print axioms root613_forbidden_parent

/-- Holdout #617: 1RB0LA_1RC---_0LD1RD_0RB0RE_0RF0LD_1LF0LA
Blocked immediate predecessor A/0 -> B/1;
there are 2 total input rows entering its halting state. -/
def root617 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, false, ⟨0, by decide⟩⟩
  | 1, false => some ⟨true, true, ⟨2, by decide⟩⟩
  | 1, true => none
  | 2, false => some ⟨false, false, ⟨3, by decide⟩⟩
  | 2, true => some ⟨true, true, ⟨3, by decide⟩⟩
  | 3, false => some ⟨false, true, ⟨1, by decide⟩⟩
  | 3, true => some ⟨false, true, ⟨4, by decide⟩⟩
  | 4, false => some ⟨false, true, ⟨5, by decide⟩⟩
  | 4, true => some ⟨false, false, ⟨3, by decide⟩⟩
  | 5, false => some ⟨true, false, ⟨5, by decide⟩⟩
  | 5, true => some ⟨false, false, ⟨0, by decide⟩⟩
  | _, _ => none

private theorem root617_entry :
    ∀ (s : Slot) (t : Move), root617 s = some t →
      t.next = ⟨0, by decide⟩ →
      t.write = false ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root617] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root617_forbidden_parent (n : Nat) (c : Config)
    (hr : run root617 n blank = some c)
    (hs : readSlot c = (⟨0, by decide⟩, false)) :
    ∃ d, rawStep root617 c = some d ∧
      d.state = ⟨1, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root617 ⟨0, by decide⟩ false
    true true ⟨1, by decide⟩ true
    (by decide) root617_entry (by decide) n c hr hs

#print axioms root617_forbidden_parent

/-- Holdout #645: 1RB1LE_0RC---_1RD0LA_1RE0RB_0LA0LF_0LD1LF
Blocked immediate predecessor A/0 -> B/1;
there are 2 total input rows entering its halting state. -/
def root645 : Machine := fun (q,b) =>
  match q.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨true, false, ⟨4, by decide⟩⟩
  | 1, false => some ⟨false, true, ⟨2, by decide⟩⟩
  | 1, true => none
  | 2, false => some ⟨true, true, ⟨3, by decide⟩⟩
  | 2, true => some ⟨false, false, ⟨0, by decide⟩⟩
  | 3, false => some ⟨true, true, ⟨4, by decide⟩⟩
  | 3, true => some ⟨false, true, ⟨1, by decide⟩⟩
  | 4, false => some ⟨false, false, ⟨0, by decide⟩⟩
  | 4, true => some ⟨false, false, ⟨5, by decide⟩⟩
  | 5, false => some ⟨false, false, ⟨3, by decide⟩⟩
  | 5, true => some ⟨true, false, ⟨5, by decide⟩⟩
  | _, _ => none

private theorem root645_entry :
    ∀ (s : Slot) (t : Move), root645 s = some t →
      t.next = ⟨0, by decide⟩ →
      t.write = false ∧ t.right = false := by
  intro ⟨st,b⟩ t ht hn
  have hst : st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 := by
    have hb := st.isLt
    omega
  rcases hst with hq|hq|hq|hq|hq|hq <;> subst st <;>
    cases b <;> simp [root645] at ht <;> cases ht <;> simp_all

/-- Genuine blank-root impossibility of the listed immediate halting
predecessor, uniformly for every successful raw time. -/
theorem root645_forbidden_parent (n : Nat) (c : Config)
    (hr : run root645 n blank = some c)
    (hs : readSlot c = (⟨0, by decide⟩, false)) :
    ∃ d, rawStep root645 c = some d ∧
      d.state = ⟨1, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbidden_transition root645 ⟨0, by decide⟩ false
    true true ⟨1, by decide⟩ true
    (by decide) root645_entry (by decide) n c hr hs

#print axioms root645_forbidden_parent

end BB6Overwrite
