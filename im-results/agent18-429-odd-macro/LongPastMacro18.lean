import Q0MacroCore

namespace BB429Q0Macro

set_option maxRecDepth 30000
set_option maxHeartbeats 30000000

/-- A concrete, fixed finite macro word uses the exact original signed
    radix-16 operations rather than an independent simulator. -/
def IsWord : List Digit → Nat → Nat → Bool
  | [], _, _ => true
  | d :: ds, p, y => decide (num d p y % 16 = 0) &&
    IsWord ds (nextP d p) (nextY d p y)

/-- Soundness of the small arithmetic checker for the source Path semantics. -/
theorem path_of_word : ∀ (ds : List Digit) (p y : Nat),
    IsWord ds p y = true → Path ds.length p y := by
  intro ds
  induction ds with
  | nil =>
    intro p y _
    exact Path.nil p y
  | cons d ds ih =>
    intro p y h
    change decide (num d p y % 16 = 0) &&
      IsWord ds (nextP d p) (nextY d p y) = true at h
    cases hx : decide (num d p y % 16 = 0) with
    | false =>
      simp [hx] at h
    | true =>
      have hmod : num d p y % 16 = 0 := of_decide_true hx
      have htail : IsWord ds (nextP d p) (nextY d p y) = true := by
        simpa [hx] using h
      simpa only [List.length_cons] using
        (Path.cons d hmod (ih (nextP d p) (nextY d p y) htail))

/-- The s=0 instance of the infinite 3k inverse family, paired into
    source q0 macro digits: 0^6,5,1,0^7,1,0^8. -/
def witness18 : List Digit :=
  List.replicate 6 .zero ++ [.five, .one] ++
  List.replicate 7 .zero ++ [.one] ++ List.replicate 8 .zero

/-- A genuine radix-16 macro path of length 24 from the explicit
    2*4^18+4 height-two inverse ancestor. This is synthetic, NOT blank-root. -/
theorem witness18_path : Path 24 (4^18 - 77) (1015 * 4^12) := by
  have hw : IsWord witness18 (4^18 - 77) (1015 * 4^12) = true := by decide
  simpa [witness18] using path_of_word witness18 (4^18 - 77) (1015 * 4^12) hw

def runWord : List Digit → Nat → Nat → Nat × Nat
  | [], p, y => (p,y)
  | d::ds,p,y => runWord ds (nextP d p) (nextY d p y)

theorem witness18_endpoint :
    runWord witness18 (4^18 - 77) (1015 * 4^12) = (4^18 + 2, 1) := by
  decide

#print axioms path_of_word
#print axioms witness18_path
#print axioms witness18_endpoint

end BB429Q0Macro
