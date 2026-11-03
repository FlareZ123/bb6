import ChampionModular
import Lean.Elab.Tactic.Omega

namespace BB6ChampionArithmetic

/-- Number of trailing zero bits, with v₂(0)=0 by convention. -/
def v2 (n : Nat) : Nat :=
  if h : n ≤ 1 then 0
  else if n % 2 = 0 then 1 + v2 (n / 2) else 0
termination_by n
decreasing_by omega

/-- Proposed TM63 successful-step cost for one Rst0/1/2. UNPROVED AS RAW COST. -/
def proposedIncrementCost (m n a b : Nat) : Nat :=
  6*4^b + 42*2^b + 15 + 4*m +12*(a+v2 n) - 9*b

structure SectionResult where
  marker : Nat
  exponent : Nat
  right : Nat
  cost : Nat
  deriving Repr

def nextMarker (m : Nat) : Nat := (m+2)%3
def nextExponent (m a b : Nat) : Nat := a+b+(if m % 3 = 0 then 1 else 2)
def nextRight (b : Nat) : Nat := 2^b-1

/-- Source-syntactic endpoint recurrence together with UNPROVED candidate costs. -/
def sectionResult : Nat → Nat → Nat → Nat → SectionResult
  | 0, m, a, b => ⟨m%3, a, b, 0⟩
  | n+1, m, a, b =>
    let m' := nextMarker m
    let a' := nextExponent m a b
    let b' := nextRight b
    let rest := sectionResult n m' a' b'
    { rest with cost := proposedIncrementCost (m%3) (n+1) a b + rest.cost }

/-- Final marker depends solely on number of decrements, with no huge eval. -/
theorem sectionResult_marker (n m a b : Nat) :
    (sectionResult n m a b).marker = (m+2*n)%3 := by
  induction n generalizing m a b with
  | zero => simp [sectionResult]
  | succ n ih =>
    simp only [sectionResult]
    rw [ih]
    simp only [nextMarker]
    omega

theorem sectionResult_marker_one (k a b : Nat) :
    (sectionResult (3*k+1) 2 a b).marker = 1 := by
  rw [sectionResult_marker]
  omega

theorem sectionResult_marker_two (k a b : Nat) :
    (sectionResult (3*k+2) 2 a b).marker = 0 := by
  rw [sectionResult_marker]
  omega

def resetCost (length exponent right : Nat) : Nat :=
  12*(length+exponent) + 6*4^right + 42*2^right+49-9*right

def terminalCost (length exponent : Nat) : Nat := 59+12*(length+exponent)

/-- Candidate champion primitive step count from observed costs. NO RUNTIME PROOF:
    raw TM macro costs, full-source machine bridge and count remain unproved.
    The function is total but intentionally not evaluated at this huge input. -/
def proposedTM63Moves : Nat :=
  let first := sectionResult 7 2 6 63
  let length1 := 3+first.exponent+2
  let index1 := resetIndex 3 first.exponent
  let middle := sectionResult index1 2 first.right (nextRight first.right)
  let length2 := length1+middle.exponent+2
  let index2 := resetIndex length1 middle.exponent
  let last := sectionResult index2 2 middle.right (nextRight middle.right)
  27959 + first.cost + resetCost 3 first.exponent first.right +
    middle.cost + resetCost length1 middle.exponent middle.right +
    last.cost + terminalCost length2 last.exponent

/-- BB6Coverage counts the final undefined halting query as the last step. -/
def proposedTM63Score : Nat := proposedTM63Moves + 1

/-- Six more successful moves for the rooted champion, by Agent48's verified
    exact A9/E15 join. This is still only a proposed score, not a run theorem. -/
def proposedChampionScore : Nat := proposedTM63Moves + 7


/-- Number of parity flips in the successful-decrement exponent recurrence. -/
def exponentFlipCount : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, m => (if m%3=0 then 0 else 1) + exponentFlipCount n (nextMarker m)

theorem nextRight_odd (b : Nat) (hb : b%2=1) :
    (nextRight b)%2=1 := by
  have hp : 0 < b := by omega
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  subst b
  simp only [nextRight, Nat.pow_succ]
  have hpow : 0 < 2^k := Nat.pow_pos (by decide)
  omega

theorem sectionResult_exponent_parity (n m a b : Nat) (hb : b%2=1) :
    (sectionResult n m a b).exponent%2 = (a+exponentFlipCount n m)%2 := by
  induction n generalizing m a b with
  | zero => simp [sectionResult, exponentFlipCount]
  | succ n ih =>
    have hod := nextRight_odd b hb
    simp only [sectionResult, exponentFlipCount]
    change (sectionResult n (nextMarker m) (nextExponent m a b) (nextRight b)).exponent %2 = _
    rw [ih _ _ _ hod]
    unfold nextExponent
    split <;> omega

/-- Huge first-stage exponent parity without evaluating any giant tower. -/
theorem first_stage_exponent_odd :
    (sectionResult 7 2 6 63).exponent%2 = 1 := by
  have h := sectionResult_exponent_parity 7 2 6 63 (by decide)
  have hflip : exponentFlipCount 7 2 = 5 := by decide
  rw [hflip] at h
  have he : (6+5)%2=1 := by decide
  rw [he] at h
  exact h


private theorem first_reset_length_even :
    (3+(sectionResult 7 2 6 63).exponent+2)%2 = 0 := by
  have h := first_stage_exponent_odd
  omega

/-- The actual first reset index is of type 3k+1. -/
theorem first_reset_index_one :
    resetIndex 3 (sectionResult 7 2 6 63).exponent %3 = 1 := by
  have h := first_stage_exponent_odd
  obtain ⟨k, hk⟩ : ∃ k, (sectionResult 7 2 6 63).exponent=2*k+1 := by
    refine ⟨(sectionResult 7 2 6 63).exponent/2, ?_⟩
    omega
  rw [hk]
  exact odd_length_odd_exponent_reset 1 k

/-- After consuming the enormous first reset index, the marker is m1. -/
theorem middle_stage_marker_one :
    (sectionResult (resetIndex 3 (sectionResult 7 2 6 63).exponent)
      2 (sectionResult 7 2 6 63).right
      (nextRight (sectionResult 7 2 6 63).right)).marker = 1 := by
  rw [sectionResult_marker]
  have hr := first_reset_index_one
  omega

/-- The length after first reset is even, so the second reset index is 3k+2. -/
theorem second_reset_index_two :
    resetIndex (3+(sectionResult 7 2 6 63).exponent+2)
      (sectionResult (resetIndex 3 (sectionResult 7 2 6 63).exponent)
        2 (sectionResult 7 2 6 63).right
        (nextRight (sectionResult 7 2 6 63).right)).exponent %3 = 2 := by
  have he := first_reset_length_even
  obtain ⟨k,hk⟩ : ∃ k, 3+(sectionResult 7 2 6 63).exponent+2=2*k := by
    refine ⟨(3+(sectionResult 7 2 6 63).exponent+2)/2, ?_⟩
    omega
  rw [hk]
  exact even_length_reset k _

/-- Hence after the second counted decrement stage, the marker is m0. -/
theorem final_stage_marker_zero :
    (sectionResult
      (resetIndex (3+(sectionResult 7 2 6 63).exponent+2)
        (sectionResult (resetIndex 3 (sectionResult 7 2 6 63).exponent)
          2 (sectionResult 7 2 6 63).right
          (nextRight (sectionResult 7 2 6 63).right)).exponent)
      2 0 1).marker=0 := by
  rw [sectionResult_marker]
  have hr := second_reset_index_two
  omega

#print axioms sectionResult_marker
#print axioms sectionResult_marker_one
#print axioms sectionResult_marker_two
#print axioms first_stage_exponent_odd
#print axioms first_reset_index_one
#print axioms middle_stage_marker_one
#print axioms second_reset_index_two
#print axioms final_stage_marker_zero

end BB6ChampionArithmetic
