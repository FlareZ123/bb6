import RayFinite
import Lean.Elab.Tactic.Omega

namespace BB6Coverage

/-- The already-visited interval strictly to the left of the A-head
contains no adjacent pair of blank cells. -/
def leftPrefixNo00 (c : FinRayCfg) (lo : Int) : Prop :=
  ∀ x, lo <= x → x + 1 < c.head →
    finiteTape c x = true ∨ finiteTape c (x+1) = true

/-- If the head is to the right of the left frontier, the frontier cell
is marked. -/
def leftFrontierOne (c : FinRayCfg) (lo : Int) : Prop :=
  lo < c.head → finiteTape c lo = true

/-- At the frontier itself, the current cell is blank. -/
def frontierHeadZero (c : FinRayCfg) (lo : Int) : Prop :=
  lo = c.head → finiteTape c c.head = false

/-- Under the empirical left-prefix invariant, an A/1 visit cannot have
two blank cells immediately to its left. This is the local obstruction to
the only F/0 halting route. The proof separates frontier distance 0, 1,
and at least 2. -/
theorem a1_left_pair_not00 (c : FinRayCfg) (lo : Int)
    (hfront : lo <= c.head)
    (hprefix : leftPrefixNo00 c lo)
    (hfrontier : leftFrontierOne c lo)
    (hzero : frontierHeadZero c lo)
    (hcurrent : finiteTape c c.head = true) :
    finiteTape c (c.head-1) = true ∨
      finiteTape c (c.head-2) = true := by
  by_cases h0 : lo = c.head
  · have hz := hzero h0
    simp [hz] at hcurrent
  · by_cases h1 : lo + 1 = c.head
    · have hlo : lo < c.head := by omega
      have hone := hfrontier hlo
      have hpos : c.head - 1 = lo := by omega
      exact Or.inl (by simpa [hpos] using hone)
    · have hgap : lo + 2 <= c.head := by omega
      have hno := hprefix (c.head-2) (by omega) (by omega)
      exact hno.elim (fun h => Or.inr h) (fun h => Or.inl h)

/-- Equivalent form: the F/0 precondition (two blanks immediately left
of an A/1 head) is impossible under the prefix invariant. -/
theorem a1_cannot_enter_f0 (c : FinRayCfg) (lo : Int)
    (hfront : lo <= c.head)
    (hprefix : leftPrefixNo00 c lo)
    (hfrontier : leftFrontierOne c lo)
    (hzero : frontierHeadZero c lo)
    (hcurrent : finiteTape c c.head = true) :
    ¬ (finiteTape c (c.head-1) = false ∧
       finiteTape c (c.head-2) = false) := by
  intro hblank
  have hpair := a1_left_pair_not00 c lo hfront hprefix hfrontier hzero hcurrent
  rcases hpair with hleft | hleft
  · simp [hblank.1] at hleft
  · simp [hblank.2] at hleft

#print axioms a1_left_pair_not00
#print axioms a1_cannot_enter_f0

end BB6Coverage
