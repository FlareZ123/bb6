import OneHalt
import BB6Coverage

namespace BB6.CoverageAdapter

/-- Converts Agent13's canonical 25-choice normalized table into Agent8's machine. -/
def toAgent8Machine (m : BB6.Coverage.SimpleMachine) : BB6Coverage.Machine :=
  fun slot => (m slot.1 slot.2).map (fun (w, d, q) =>
    { write := w, right := d, next := q })

def toAgent13Machine (m : BB6Coverage.Machine) : BB6.Coverage.SimpleMachine :=
  fun q b => (m (q,b)).map (fun i => (i.write, i.right, i.next))

theorem toAgent13_toAgent8 (m : BB6.Coverage.SimpleMachine) :
    toAgent13Machine (toAgent8Machine m) = m := by
  funext q b
  cases h : m q b with
  | none => simp [toAgent8Machine, toAgent13Machine, h]
  | some p =>
    rcases p with ⟨w,d,s⟩
    simp [toAgent8Machine, toAgent13Machine, h]

theorem toAgent8_toAgent13 (m : BB6Coverage.Machine) :
    toAgent8Machine (toAgent13Machine m) = m := by
  funext slot
  cases h : m slot with
  | none => simp [toAgent8Machine, toAgent13Machine, h]
  | some p =>
    cases p with
    | mk w d s => simp [toAgent8Machine, toAgent13Machine, h]

def toAgent8Config (c : BB6.Coverage.Config) : BB6Coverage.Config :=
  { state := c.state, head := c.head, tape := c.tape }

def toAgent13Config (c : BB6Coverage.Config) : BB6.Coverage.Config :=
  { state := c.state, head := c.head, tape := c.tape }

@[simp] theorem toAgent13Config_toAgent8Config (c : BB6.Coverage.Config) :
    toAgent13Config (toAgent8Config c) = c := by cases c; rfl

@[simp] theorem toAgent8Config_toAgent13Config (c : BB6Coverage.Config) :
    toAgent8Config (toAgent13Config c) = c := by cases c; rfl

private theorem raw_step_agree (m : BB6.Coverage.SimpleMachine) (c : BB6.Coverage.Config) :
    BB6Coverage.rawStep (toAgent8Machine m) (toAgent8Config c) =
      (BB6.Coverage.tick m c).map toAgent8Config := by
  unfold BB6Coverage.rawStep BB6.Coverage.tick
  cases h : m c.state (c.tape c.head) with
  | none => simp [toAgent8Machine, toAgent8Config, BB6Coverage.readSlot, h]
  | some p =>
    rcases p with ⟨w,d,q⟩
    cases d <;> simp [toAgent8Machine, toAgent8Config,
      BB6Coverage.readSlot, BB6Coverage.applyMove, h] <;> omega

/-- Both representations execute identical full infinite-tape blank computations. -/
theorem run_agree (m : BB6.Coverage.SimpleMachine) (n : Nat) :
    BB6Coverage.run (toAgent8Machine m) n BB6Coverage.blank =
      (BB6.Coverage.run (BB6.Coverage.tick m) n).map toAgent8Config := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [BB6Coverage.run, BB6.Coverage.run, ih]
    cases h : BB6.Coverage.run (BB6.Coverage.tick m) n with
    | none => simp [h]
    | some c => simp [h, raw_step_agree]

end BB6.CoverageAdapter
