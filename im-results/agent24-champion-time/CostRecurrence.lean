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

def resetIndex (length exponent : Nat) : Nat :=
  (4*2^length-1)*2^exponent-1

def resetCost (length exponent right : Nat) : Nat :=
  12*(length+exponent) + 6*4^right + 42*2^right+49-9*right

def terminalCost (length exponent : Nat) : Nat := 59+12*(length+exponent)

/-- Candidate champion primitive step count from observed costs. NO RUNTIME PROOF:
    raw TM macro costs, full-source machine bridge and count remain unproved.
    The function is total but intentionally not evaluated at this huge input. -/
def proposedChampionMoves : Nat :=
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
def proposedChampionScore : Nat := proposedChampionMoves + 1

#print axioms sectionResult_marker
#print axioms sectionResult_marker_one
#print axioms sectionResult_marker_two

end BB6ChampionArithmetic
