import Q0MacroCore

namespace BB429Q0Macro

set_option maxRecDepth 30000
set_option maxHeartbeats 30000000

def IsWord683 : List Digit → Nat → Nat → Bool
  | [], _, _ => true
  | d::ds,p,y =>
      decide (num d p y % 16 = 0) &&
      IsWord683 ds (nextP d p) (nextY d p y)

theorem pathOfWord683 : ∀ (ds : List Digit) (p y : Nat),
    IsWord683 ds p y = true → Path ds.length p y := by
  intro ds
  induction ds with
  | nil =>
    intro p y _
    exact Path.nil p y
  | cons d ds ih =>
    intro p y h
    change decide (num d p y % 16 = 0) &&
      IsWord683 ds (nextP d p) (nextY d p y) = true at h
    by_cases hd : num d p y % 16 = 0
    · have ht : IsWord683 ds (nextP d p) (nextY d p y) = true := by
        simpa [hd] using h
      simpa only [List.length_cons] using
        (Path.cons d hd (ih (nextP d p) (nextY d p y) ht))
    · simp [hd] at h

/-- m=340 in the all-odd-exponent strict source window family.
    The chronological past word is only 0^340,4,0; the future 0^340. -/
def past683 : List Digit := List.replicate 340 .zero ++ [.four,.zero]
def future683 : List Digit := List.replicate 340 .zero

theorem past683_path :
    Path 342 (4^683 - 1027) (10 * 16^340) := by
  have hw : IsWord683 past683 (4^683 - 1027) (10 * 16^340) = true := by decide
  simpa [past683] using
    pathOfWord683 past683 (4^683 - 1027) (10 * 16^340) hw

def run683 : List Digit → Nat → Nat → Nat × Nat
  | [],p,y => (p,y)
  | d::ds,p,y => run683 ds (nextP d p) (nextY d p y)

theorem past683_endpoint :
    run683 past683 (4^683 - 1027) (10 * 16^340)
      = (4^683, 16^340) := by decide

theorem future683_path :
    Path 340 (4^683) (16^340) := by
  have hw : IsWord683 future683 (4^683) (16^340) = true := by decide
  simpa [future683] using
    pathOfWord683 future683 (4^683) (16^340) hw

theorem future683_endpoint :
    run683 future683 (4^683) (16^340)
      = (4^683 + 1020, 1) := by decide

theorem twoSided683 :
    Path 342 (4^683 - 1027) (10 * 16^340) ∧
    run683 past683 (4^683 - 1027) (10 * 16^340)
      = (4^683, 16^340) ∧
    Path 340 (4^683) (16^340) ∧
    run683 future683 (4^683) (16^340)
      = (4^683 + 1020, 1) := by
  exact ⟨past683_path,past683_endpoint,
         future683_path,future683_endpoint⟩

theorem initial683_strict :
    0 < 10 * 16^340 ∧
    3 * (10 * 16^340) < 4^683 - 1027 := by decide

#print axioms pathOfWord683
#print axioms twoSided683
#print axioms initial683_strict

end BB429Q0Macro
