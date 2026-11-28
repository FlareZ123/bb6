import Q0MacroCore

namespace BB429Q0Macro

set_option maxRecDepth 30000
set_option maxHeartbeats 30000000

/-- Computable exact-divisibility certificate for a source q0 macro word. -/
def IsWord430 : List Digit → Nat → Nat → Bool
  | [], _, _ => true
  | d :: ds, p, y => decide (num d p y % 16 = 0) &&
    IsWord430 ds (nextP d p) (nextY d p y)

theorem pathOfWord430 : ∀ (ds : List Digit) (p y : Nat),
    IsWord430 ds p y = true → Path ds.length p y := by
  intro ds
  induction ds with
  | nil =>
    intro p y _
    exact Path.nil p y
  | cons d ds ih =>
    intro p y h
    change decide (num d p y % 16 = 0) &&
      IsWord430 ds (nextP d p) (nextY d p y) = true at h
    by_cases hd : num d p y % 16 = 0
    · have htail : IsWord430 ds (nextP d p) (nextY d p y) = true := by
        simpa [hd] using h
      simpa only [List.length_cons] using
        (Path.cons d hd (ih (nextP d p) (nextY d p y) htail))
    · simp [hd] at h

/-- Exact paired signed macro witness for s=2 in LongPastCascade:
    chronological word 0^197,1,4,0,5,0^211,5,1,0^212,1,0^113. -/
def witness430 : List Digit :=
  List.replicate 197 .zero ++ [.one,.four,.zero,.five] ++
  List.replicate 211 .zero ++ [.five,.one] ++
  List.replicate 212 .zero ++ [.one] ++
  List.replicate 113 .zero

/-- A source-aligned signed macro path of exactly 740 steps ending
    at (4^430+2,4^202). This is a synthetic path, not blank ancestry. -/
theorem witness430_path :
    Path 740 (4^430 - 2231) (33316354 * 4^394) := by
  have hw : IsWord430 witness430 (4^430 - 2231) (33316354 * 4^394) = true := by
    decide
  simpa [witness430] using
    pathOfWord430 witness430 (4^430 - 2231) (33316354 * 4^394) hw

def run430 : List Digit → Nat → Nat → Nat × Nat
  | [], p, y => (p,y)
  | d :: ds,p,y => run430 ds (nextP d p) (nextY d p y)

theorem witness430_endpoint :
    run430 witness430 (4^430 - 2231) (33316354 * 4^394)
       = (4^430 + 2, 4^202) := by
  decide

/-- Exactly 101 forward zero macros survive after the center. -/
def forward430 : List Digit := List.replicate 101 .zero

theorem forward430_path :
    Path 101 (4^430 + 2) (4^202) := by
  have hw : IsWord430 forward430 (4^430 + 2) (4^202) = true := by
    decide
  simpa [forward430] using
    pathOfWord430 forward430 (4^430 + 2) (4^202) hw

theorem forward430_endpoint :
    run430 forward430 (4^430 + 2) (4^202) = (4^430 + 305, 1) := by
  decide

/-- A 101-step symmetric exact signed macro crossing of the coefficient-2
    near-power center. The past has a longer 740-step history. All vertices
    are strict by Q0MacroCore.interior_step and the initial cone check.
    Synthetic graph witness only: no blank-root source reachability. -/
theorem witness430_two_sided :
    Path 740 (4^430 - 2231) (33316354 * 4^394) ∧
    run430 witness430 (4^430 - 2231) (33316354 * 4^394)
      = (4^430 + 2, 4^202) ∧
    Path 101 (4^430 + 2) (4^202) ∧
    run430 forward430 (4^430 + 2) (4^202)
      = (4^430 + 305, 1) := by
  exact ⟨witness430_path,witness430_endpoint,
         forward430_path,forward430_endpoint⟩

theorem witness430_initial_interior :
    0 < 33316354 * 4^394 ∧
    3*(33316354 * 4^394) < 4^430-2231 := by
  decide

#print axioms forward430_path
#print axioms forward430_endpoint
#print axioms witness430_two_sided
#print axioms witness430_initial_interior

#print axioms pathOfWord430
#print axioms witness430_path
#print axioms witness430_endpoint

end BB429Q0Macro
