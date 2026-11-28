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


/-- Deterministic front-weight update for a B triad. -/
def bNextWeight (ell w : Nat) : Nat :=
  if ell % 8 = 6 then w + 1 else w

/-- Deterministic front-weight update for an A-carry triad. -/
def carryNextWeight (ell w : Nat) : Nat :=
  if ell % 8 = 7 then w - 1 else w

/-- Unified scalar B law: residue 6 increments the weight, all other
    residues preserve it. -/
theorem b_weighted_transition (ell w : Nat)
    (h7 : 7 ≤ ell)
    (hbound : 8 * bNextWeight ell w ≤ rhoZero (ell - 7)) :
    weightedZero ell w - 15 =
      weightedZero (ell - 7) (bNextWeight ell w) := by
  by_cases h6 : ell % 8 = 6
  · simp [bNextWeight, h6]
    exact b_exception_increments ell w h7 h6 (by simpa [bNextWeight, h6] using hbound)
  · simp [bNextWeight, h6]
    exact b_regular_preserves ell w h7 h6 (by simpa [bNextWeight, h6] using hbound)

/-- Unified scalar carry law: residue 7 decrements a positive weight, all
    other residues preserve it. -/
theorem carry_weighted_transition (ell w : Nat)
    (h1 : 1 ≤ ell)
    (hpositive : ell % 8 = 7 → 1 ≤ w)
    (hbound : 8 * carryNextWeight ell w ≤ rhoZero (ell - 1)) :
    weightedZero ell w - 1 =
      weightedZero (ell - 1) (carryNextWeight ell w) := by
  by_cases h7 : ell % 8 = 7
  · simp [carryNextWeight, h7]
    exact carry_exception_decrements ell w h1 h7 (hpositive h7)
      (by simpa [carryNextWeight, h7] using hbound)
  · simp [carryNextWeight, h7]
    exact carry_regular_preserves ell w h1 h7
      (by simpa [carryNextWeight, h7] using hbound)

/-- The abstract B-side bound is exactly the semantic runway condition:
    the high front zero-run has at least fifteen cells for the BBA block. -/
theorem b_safe_iff (ell w : Nat) (h7 : 7 ≤ ell) :
    15 ≤ weightedZero ell w ↔
      8 * bNextWeight ell w ≤ rhoZero (ell - 7) := by
  unfold weightedZero bNextWeight rhoZero
  by_cases h6 : ell % 8 = 6
  · simp [h6]
    split <;> omega
  · simp [h6]
    split <;> split <;> omega

/-- With the necessary residue-7 positivity guard, the abstract carry bound is
    exactly the semantic condition that the high front zero-run is nonempty. -/
theorem carry_safe_iff (ell w : Nat) (h1 : 1 ≤ ell)
    (hpositive : ell % 8 = 7 → 1 ≤ w) :
    1 ≤ weightedZero ell w ↔
      8 * carryNextWeight ell w ≤ rhoZero (ell - 1) := by
  by_cases h7 : ell % 8 = 7
  · have hw := hpositive h7
    have hr := rho_c_exception ell h1 h7
    simp [carryNextWeight, h7]
    unfold weightedZero
    omega
  · have hr := rho_c_regular ell h1 h7
    simp [carryNextWeight, h7]
    unfold weightedZero
    omega

/-- Normal A prepends exactly the unmarked zero-run predicted by the
    reachable second-right-run residue class. -/
theorem normalA_push {low weights high : List Nat} (b : Nat)
    (h : DefectStack low weights high)
    (h6 : 6 ≤ b) (hr : b % 8 = 5) :
    DefectStack ((b-6)::low) (0::weights) ((2*b-11)::high) := by
  have hz := rho_a_normal b h6 hr
  simpa [hz] using push_zero h (b-6)

/-- At the exact B-pop runway length, the semantic high-side BBA guard
    forces the disappearing front weight to be zero. -/
theorem b_pop_forces_zero (w : Nat)
    (h15 : 15 ≤ weightedZero 7 w) : w = 0 := by
  unfold weightedZero rhoZero at h15
  omega

/-- At the exact carry-pop runway length, high-side nonemptiness forces the
    disappearing front weight to be zero. -/
theorem carry_pop_forces_zero (w : Nat)
    (h1 : 1 ≤ weightedZero 1 w) : w = 0 := by
  unfold weightedZero rhoZero at h1
  omega

/-- Unified whole-stack B law stated directly with the semantic high-runway
    guard needed by the corresponding BBA block. -/
theorem b_weighted_stack {low weights high : List Nat} (ell w : Nat)
    (h : DefectStack low weights high)
    (h7 : 7 ≤ ell) (h15 : 15 ≤ weightedZero ell w) :
    DefectStack ((ell-7)::low) (bNextWeight ell w::weights)
      ((weightedZero ell w - 15)::high) := by
  rcases h with ⟨hlen, rfl⟩
  constructor
  · simp [hlen]
  · simp only [weightedImage]
    rw [b_weighted_transition ell w h7 ((b_safe_iff ell w h7).mp h15)]

/-- Unified whole-stack carry law stated with the semantic nonempty-run guard
    plus the necessary residue-7 positive-weight condition. -/
theorem carry_weighted_stack {low weights high : List Nat} (ell w : Nat)
    (h : DefectStack low weights high)
    (h1 : 1 ≤ ell) (hpositive : ell % 8 = 7 → 1 ≤ w)
    (hnonempty : 1 ≤ weightedZero ell w) :
    DefectStack ((ell-1)::low) (carryNextWeight ell w::weights)
      ((weightedZero ell w - 1)::high) := by
  rcases h with ⟨hlen, rfl⟩
  constructor
  · simp [hlen]
  · simp only [weightedImage]
    rw [carry_weighted_transition ell w h1 hpositive
      ((carry_safe_iff ell w h1 hpositive).mp hnonempty)]

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
#print axioms b_weighted_transition
#print axioms carry_weighted_transition
#print axioms b_safe_iff
#print axioms carry_safe_iff
#print axioms normalA_push
#print axioms b_pop_forces_zero
#print axioms carry_pop_forces_zero
#print axioms b_weighted_stack
#print axioms carry_weighted_stack
#print axioms b_exception_stack
#print axioms b_regular_stack
#print axioms carry_exception_stack
#print axioms carry_regular_stack

end BB6.Agent1Raw56.LE17557DefectStack
