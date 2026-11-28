import Raw56LE17557RhoArithmetic

namespace BB6.Agent1Raw56.LE17557DefectStack
open BB6.Agent1Raw56.LE17557RhoArithmetic

def weightedZero (z w : Nat) : Nat := rhoZero z - 8*w

def weightedImage : List Nat → List Nat → List Nat
  | [], [] => []
  | z::zs, w::ws => weightedZero z w :: weightedImage zs ws
  | _, _ => []

def DefectStack (low weights high : List Nat) : Prop :=
  weights.length = low.length ∧ high = weightedImage low weights

@[simp] theorem weightedZero_zero (z : Nat) : weightedZero z 0 = rhoZero z := by
  simp [weightedZero]

theorem push_zero {low weights high : List Nat} (h : DefectStack low weights high)
    (z : Nat) :
    DefectStack (z::low) (0::weights) (rhoZero z::high) := by
  rcases h with ⟨hlen, rfl⟩
  constructor
  · simp [hlen]
  · simp [weightedImage, weightedZero]

theorem pop {z w : Nat} {low weights highTail : List Nat}
    (h : DefectStack (z::low) (w::weights)
      (weightedZero z w :: highTail)) :
    DefectStack low weights highTail := by
  rcases h with ⟨hlen, himg⟩
  constructor
  · simpa using hlen
  · simp [weightedImage] at himg
    exact himg

theorem b_exception_increments (ell w : Nat)
    (h7 : 7 ≤ ell) (h6 : ell % 8 = 6)
    (hbound : 8*(w+1) ≤ rhoZero (ell-7)) :
    weightedZero ell w - 15 = weightedZero (ell-7) (w+1) := by
  have h := rho_b_exception ell h7 h6
  unfold weightedZero
  omega

theorem b_regular_preserves (ell w : Nat)
    (h7 : 7 ≤ ell) (h6 : ell % 8 ≠ 6)
    (hbound : 8*w ≤ rhoZero (ell-7)) :
    weightedZero ell w - 15 = weightedZero (ell-7) w := by
  have h := rho_b_regular ell h7 h6
  unfold weightedZero
  omega

theorem carry_exception_decrements (ell w : Nat)
    (h1 : 1 ≤ ell) (h7 : ell % 8 = 7) (hw : 1 ≤ w)
    (hbound : 8*(w-1) ≤ rhoZero (ell-1)) :
    weightedZero ell w - 1 = weightedZero (ell-1) (w-1) := by
  have h := rho_c_exception ell h1 h7
  unfold weightedZero
  omega

theorem carry_regular_preserves (ell w : Nat)
    (h1 : 1 ≤ ell) (h7 : ell % 8 ≠ 7)
    (hbound : 8*w ≤ rhoZero (ell-1)) :
    weightedZero ell w - 1 = weightedZero (ell-1) w := by
  have h := rho_c_regular ell h1 h7
  unfold weightedZero
  omega


/-- Whole-stack B transition at the exceptional residue: only the front
    weight changes, while every deeper zero-run/weight pair is untouched. -/
theorem b_exception_stack {low weights high : List Nat} (ell w : Nat)
    (h : DefectStack low weights high)
    (h7 : 7 ≤ ell) (h6 : ell % 8 = 6)
    (hbound : 8*(w+1) ≤ rhoZero (ell-7)) :
    DefectStack ((ell-7)::low) ((w+1)::weights)
      ((weightedZero ell w - 15)::high) := by
  rcases h with ⟨hlen, rfl⟩
  constructor
  · simp [hlen]
  · simp only [weightedImage]
    rw [b_exception_increments ell w h7 h6 hbound]

/-- Whole-stack regular B transition preserves the front weight. -/
theorem b_regular_stack {low weights high : List Nat} (ell w : Nat)
    (h : DefectStack low weights high)
    (h7 : 7 ≤ ell) (h6 : ell % 8 ≠ 6)
    (hbound : 8*w ≤ rhoZero (ell-7)) :
    DefectStack ((ell-7)::low) (w::weights)
      ((weightedZero ell w - 15)::high) := by
  rcases h with ⟨hlen, rfl⟩
  constructor
  · simp [hlen]
  · simp only [weightedImage]
    rw [b_regular_preserves ell w h7 h6 hbound]

/-- Whole-stack exceptional carry transition decrements the front weight and
    leaves every deeper pair untouched. -/
theorem carry_exception_stack {low weights high : List Nat} (ell w : Nat)
    (h : DefectStack low weights high)
    (h1 : 1 ≤ ell) (h7 : ell % 8 = 7) (hw : 1 ≤ w)
    (hbound : 8*(w-1) ≤ rhoZero (ell-1)) :
    DefectStack ((ell-1)::low) ((w-1)::weights)
      ((weightedZero ell w - 1)::high) := by
  rcases h with ⟨hlen, rfl⟩
  constructor
  · simp [hlen]
  · simp only [weightedImage]
    rw [carry_exception_decrements ell w h1 h7 hw hbound]

/-- Whole-stack regular carry transition preserves the front weight. -/
theorem carry_regular_stack {low weights high : List Nat} (ell w : Nat)
    (h : DefectStack low weights high)
    (h1 : 1 ≤ ell) (h7 : ell % 8 ≠ 7)
    (hbound : 8*w ≤ rhoZero (ell-1)) :
    DefectStack ((ell-1)::low) (w::weights)
      ((weightedZero ell w - 1)::high) := by
  rcases h with ⟨hlen, rfl⟩
  constructor
  · simp [hlen]
  · simp only [weightedImage]
    rw [carry_regular_preserves ell w h1 h7 hbound]

#print axioms push_zero
#print axioms pop
#print axioms b_exception_increments
#print axioms b_regular_preserves
#print axioms carry_exception_decrements
#print axioms carry_regular_preserves
#print axioms b_exception_stack
#print axioms b_regular_stack
#print axioms carry_exception_stack
#print axioms carry_regular_stack

end BB6.Agent1Raw56.LE17557DefectStack
