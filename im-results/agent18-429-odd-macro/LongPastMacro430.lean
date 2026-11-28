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

#print axioms pathOfWord430
#print axioms witness430_path
#print axioms witness430_endpoint

end BB429Q0Macro
