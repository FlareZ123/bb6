import Lean.Elab.Tactic.Omega

/-!
  A new exact additive cost cocycle for Raw56 leaf 17557's triad-action
  substitution. Algebraic consequences of the original A-normal,
  A-carry and B triad primitive-step formulas (see
  Raw56LE17557LocalSweeps.lean and 17557-triad-rewrite.md).

  The abstract cost identity does NOT establish that the blank orbit
  realizes every substituted action word or that the structural guards
  hold at all ranks. Those source-connected synchronization obligations
  remain open. This is the checkable quantitative bridge required to
  turn an eventual all-level conjugacy into the exact epoch clock.
-/

namespace BB6.Agent4Raw56LE17557TimeCocycle

def lastBit (b : Bool) : Nat := if b then 1 else 0

/-- A concrete low triad event, with its rightmost scanned one-run and
    whether that run is the final finite run. -/
inductive Triad
  | aNormal (a b c : Nat) (last : Bool)
  | aCarry (a c d : Nat) (last : Bool)
  | b (a b : Nat) (last : Bool)
  deriving Repr, DecidableEq

def aNormalCost (a b c : Nat) : Nat := a+b+2*c+26
def aCarryCost (a c d : Nat) : Nat := 2*a+2*c+d+33
def bCost (a b : Nat) : Nat := 2*a+2*b+29

def lowTime : Triad → Nat
  | .aNormal a b c _ => aNormalCost a b c
  | .aCarry a c d _ => aCarryCost a c d
  | .b a b _ => bCost a b

/-- Exact high-level primitive-step counts of the substituted ABA / BBA
    triad words. A rightmost one-run transforms 2c+1, a nonfinal one-run
    transforms 2c; in an ordinary internal position the second one-run
    transforms 2b+3. The high third A is a carry in all three cases.
    This abstracts only the integer costs, not the source transitions. -/
def highTime : Triad → Nat
  | .aNormal a b c last =>
      let ch := 2*c + lastBit last
      aNormalCost (2*a+2) (2*b+3) ch +
        bCost 2 (ch+5) +
        aCarryCost 2 (ch+8) 0
  | .aCarry a c d last =>
      let ch := 2*c + lastBit last
      aNormalCost (2*a+2) 13 ch +
        bCost 2 (ch+5) +
        aCarryCost 2 (ch+8) (2*a+2*d+4)
  | .b a b last =>
      bCost (2*a+2) (2*b+3+lastBit last) +
        bCost 2 5 +
        aCarryCost 2 8 0

/-- The nontrivial excess cost of three high A/B/A or B/B/A actions over
    twice the corresponding low action. Both A-normal and A-carry have
    the SAME coefficient of c, independent of left-context length. -/
def excess : Triad → Nat
  | .aNormal _ _ c last => 8*c+75+6*lastBit last
  | .aCarry _ c _ last => 8*c+75+6*lastBit last
  | .b _ _ last => 77+2*lastBit last

/-- Source-triad arithmetic gives an exact affine cocycle:
    A → ABA: high = 2*low + 8c +75 (+6 if final).
    B → BBA: high = 2*low + 77 (+2 if final). -/
theorem local_time_cocycle (e : Triad) :
    highTime e = 2*lowTime e + excess e := by
  cases e with
  | aNormal a b c last =>
      cases last <;>
        simp [highTime, lowTime, excess, aNormalCost, aCarryCost, bCost, lastBit] <;>
        omega
  | aCarry a c d last =>
      cases last <;>
        simp [highTime, lowTime, excess, aNormalCost, aCarryCost, bCost, lastBit] <;>
        omega
  | b a b last =>
      cases last <;>
        simp [highTime, lowTime, excess, aNormalCost, aCarryCost, bCost, lastBit] <;>
        omega

/-- Aggregate excess cost over arbitrary (not necessarily reachable)
    mixed rank-labelled triad words. -/
theorem word_time_cocycle (xs : List Triad) :
    (xs.map highTime).sum =
      2*(xs.map lowTime).sum + (xs.map excess).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [local_time_cocycle x, ih]
      omega

def isA : Triad → Nat
  | .aNormal .. => 1
  | .aCarry .. => 1
  | .b .. => 0

def isB : Triad → Nat
  | .b .. => 1
  | _ => 0

def thirdRun : Triad → Nat
  | .aNormal _ _ c _ => c
  | .aCarry _ c _ _ => c
  | .b .. => 0

def finalA : Triad → Nat
  | .aNormal _ _ _ last => lastBit last
  | .aCarry _ _ _ last => lastBit last
  | .b .. => 0

def finalB : Triad → Nat
  | .b _ _ last => lastBit last
  | _ => 0

/-- The cocycle is a linear combination of counts and a single
    weighted observable, the sum of third one-run lengths at A events. -/
theorem excess_decompose (e : Triad) :
    excess e =
      75*isA e + 77*isB e + 8*thirdRun e +
      6*finalA e + 2*finalB e := by
  cases e with
  | aNormal a b c last =>
      cases last <;> simp [excess,isA,isB,thirdRun,finalA,finalB,lastBit] <;> omega
  | aCarry a c d last =>
      cases last <;> simp [excess,isA,isB,thirdRun,finalA,finalB,lastBit] <;> omega
  | b a b last =>
      cases last <;> simp [excess,isA,isB,thirdRun,finalA,finalB,lastBit] <;> omega

theorem sum_excess_decompose (xs : List Triad) :
    (xs.map excess).sum =
      75*(xs.map isA).sum + 77*(xs.map isB).sum +
      8*(xs.map thirdRun).sum +
      6*(xs.map finalA).sum + 2*(xs.map finalB).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [excess_decompose x, ih]
      omega

/-- Useful future clock interface: equality of A and B counts, as in the
    proved substitution word, leaves a single unbounded additive observable
    plus two explicitly counted terminal-run corrections. -/
theorem balanced_word_cocycle (xs : List Triad)
    (hab : (xs.map isA).sum = (xs.map isB).sum) :
    (xs.map highTime).sum =
      2*(xs.map lowTime).sum +
      152*(xs.map isA).sum +
      8*(xs.map thirdRun).sum +
      6*(xs.map finalA).sum + 2*(xs.map finalB).sum := by
  rw [word_time_cocycle, sum_excess_decompose]
  omega

#print axioms local_time_cocycle
#print axioms word_time_cocycle
#print axioms excess_decompose
#print axioms sum_excess_decompose
#print axioms balanced_word_cocycle

end BB6.Agent4Raw56LE17557TimeCocycle
