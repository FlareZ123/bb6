import Q0MacroCore

namespace BB429Q0Macro

set_option maxRecDepth 30000
set_option maxHeartbeats 30000000

/-- Exact computable original q0 signed radix-16 step certificate. -/
def IsWord684 : List Digit → Nat → Nat → Bool
  | [], _, _ => true
  | d::ds,p,y =>
      decide (num d p y % 16 = 0) &&
      IsWord684 ds (nextP d p) (nextY d p y)

theorem pathOfWord684 : ∀ (ds : List Digit) (p y : Nat),
    IsWord684 ds p y = true → Path ds.length p y := by
  intro ds
  induction ds with
  | nil =>
    intro p y _
    exact Path.nil p y
  | cons d ds ih =>
    intro p y h
    change decide (num d p y % 16 = 0) &&
      IsWord684 ds (nextP d p) (nextY d p y) = true at h
    by_cases hd : num d p y % 16 = 0
    · have ht : IsWord684 ds (nextP d p) (nextY d p y) = true := by
        simpa [hd] using h
      simpa only [List.length_cons] using
        (Path.cons d hd (ih (nextP d p) (nextY d p y) ht))
    · simp [hd] at h

/-- R=6 in the minimal coefficient-two/b=2 Cantor double-cancellation.
    Chronological paired word: 0^286,5,0,4,0^339,1,0^341,1,0.
    Inverse length 1944 halfsteps, or 972 signed source macros. -/
def past684 : List Digit :=
  List.replicate 286 .zero ++ [.five,.zero,.four] ++
  List.replicate 339 .zero ++ [.one] ++
  List.replicate 341 .zero ++ [.one,.zero]

def future684 : List Digit := List.replicate 340 .zero

theorem past684_path :
    Path 972 (4^684 - 2923) (2111029 * 4^572) := by
  have hw : IsWord684 past684 (4^684 - 2923) (2111029 * 4^572) = true := by
    decide
  simpa [past684] using
    pathOfWord684 past684 (4^684 - 2923) (2111029 * 4^572) hw

def run684 : List Digit → Nat → Nat → Nat × Nat
  | [],p,y => (p,y)
  | d::ds,p,y => run684 ds (nextP d p) (nextY d p y)

theorem past684_endpoint :
    run684 past684 (4^684 - 2923) (2111029 * 4^572)
      = (4^684 + 1, 4^680) := by decide

theorem future684_path :
    Path 340 (4^684 + 1) (4^680) := by
  have hw : IsWord684 future684 (4^684 + 1) (4^680) = true := by
    decide
  simpa [future684] using
    pathOfWord684 future684 (4^684 + 1) (4^680) hw

theorem future684_endpoint :
    run684 future684 (4^684 + 1) (4^680)
      = (4^684 + 1021, 1) := by decide

/-- Certified exact 340-step *symmetric* signed source macro window at
    (4^684+1,4^680). No original blank-root reachability is asserted. -/
theorem twoSided684 :
    Path 972 (4^684 - 2923) (2111029 * 4^572) ∧
    run684 past684 (4^684 - 2923) (2111029 * 4^572)
      = (4^684 + 1, 4^680) ∧
    Path 340 (4^684 + 1) (4^680) ∧
    run684 future684 (4^684 + 1) (4^680)
      = (4^684 + 1021, 1) := by
  exact ⟨past684_path,past684_endpoint,
         future684_path,future684_endpoint⟩

theorem initial684_strict :
    0 < 2111029 * 4^572 ∧
    3 * (2111029 * 4^572) < 4^684 - 2923 := by
  decide

#print axioms pathOfWord684
#print axioms past684_path
#print axioms past684_endpoint
#print axioms future684_path
#print axioms future684_endpoint
#print axioms twoSided684
#print axioms initial684_strict

end BB429Q0Macro
