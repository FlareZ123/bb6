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

end BB6.CoverageAdapter
