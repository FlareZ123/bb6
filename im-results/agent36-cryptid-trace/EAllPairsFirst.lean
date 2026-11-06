import EZeroFirstComplete

namespace BB6.Agent36EAllPairs
open CryptidBoundary BB6.Agent36PositiveFirst
open BB6.Agent36EZeroPairs0

set_option maxHeartbeats 100000000
set_option maxRecDepth 8192

/-- All E words with a leading variable count of 10-pairs before the 110
    marker, followed by r more 10-pairs and a zero. -/
def suffix (q r : Nat) (ys : List Bool) : List Bool :=
  pairs q ++ ([true,true,false] ++ (pairs r ++ (false::ys)))

def entry (k q r : Nat) (ys : List Bool) : Cfg :=
  init (List.replicate (3*k+2) true ++ (false::suffix q r ys))

def firstTime (k q r : Nat) : Nat :=
  match q with
  | 0 => 12*k*k+49*k+96+4*r
  | q+1 => 12*k*k+49*k+64+4*q+4*r

def outUnary (k q : Nat) : Nat :=
  match q with
  | 0 => 8*k+3
  | _+1 => 8*k+5

def outSuffix (q r : Nat) (ys : List Bool) : List Bool :=
  match q with
  | 0 => packetZero ++ (List.replicate (2*r) true ++ ys)
  | q+1 => false :: (List.replicate (2*q+4) true ++
       (false :: (List.replicate (2*r+6) true ++ ys)))

def result (k q r : Nat) (ys : List Bool) : Cfg :=
  ⟨[],false,List.replicate (outUnary k q) true ++
    outSuffix q r ys,5⟩

/-- Source-certified *first* positive physical F/0 return for the complete
    two-parameter regular-language E sector 0(10)^q110(10)^r0, with arbitrary
    trailing data. The q=0 exception genuinely differs from q>=1. -/
theorem first_all_pairs (k q r : Nat) (ys : List Bool) :
    run (firstTime k q r) (entry k q r ys) = result k q r ys
    ∧ (∀ t : Nat, 0<t → t<firstTime k q r →
        ¬ PhysicalF0 (run t (entry k q r ys))) := by
  cases q with
  | zero =>
      exact BB6.Agent36EZeroFirst.originalEZeroFirst k r ys
  | succ q =>
      exact BB6.Agent36PositiveFirst.originalEPositiveFirst k q r ys

/-- Exact quadratic time cocycle, both E branches, independent of q/r/y. -/
theorem firstTime_shift (k q r : Nat) :
    firstTime (k+1) q r = firstTime k q r + (24*k+61) := by
  cases q <;> simp only [firstTime, Nat.mul_add, Nat.add_mul] <;> omega

/-- The whole E-sector first-return unary count grows by 8 when the
    original F/0 input unary count grows by 3. -/
theorem outUnary_shift (k q : Nat) :
    outUnary (k+1) q = outUnary k q + 8 := by
  cases q <;> simp only [outUnary] <;> omega

#print axioms first_all_pairs
#print axioms firstTime_shift
#print axioms outUnary_shift
end BB6.Agent36EAllPairs
