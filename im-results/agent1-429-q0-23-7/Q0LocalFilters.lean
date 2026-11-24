import Q0Converse

namespace BB429Q0Macro
set_option maxHeartbeats 10000000

/-- Existing positive-root residue tests used in the depth-16 inverse sieve,
    augmented by the additional 9,5 exclusion modulo 16 and 8. -/
def localFilters (a b : Int) : Prop :=
  ((a%8=0 → b%4=0 ∨ b%4=2) ∧
   (a%8=1 → b%4=0 ∨ b%4=1 ∨ b%4=2) ∧
   (a%8=2 → b%4=2) ∧
   (a%8=3 → b%4=1 ∨ b%4=2 ∨ b%4=3) ∧
   (a%8=4 → b%4=2) ∧
   (a%8=6 → b%4=2) ∧
   (a%8=7 → b%4=2 ∨ b%4=3)) ∧
  (a%2=0 → b%8=2) ∧
  (a%8=7 → b%8≠7) ∧
  (a%16=1 → b%8≠6) ∧
  (a%16=5 → b%8≠6) ∧
  (a%32=5 → b%16≠1) ∧
  (a%16=11 → b%8=2 ∨ b%8=6 ∨ b%8=7) ∧
  (a%32=19 → b%8=2 ∨ b%8=7) ∧
  (a%32=27 → b%8=2 ∨ b%8=7) ∧
  (a%16=15 → b%32≠26) ∧
  (a%32=15 → b%32≠24) ∧
  (a%32=31 → b%32≠24) ∧
  (a%32=1 → b%32≠25) ∧
  (a%64=1 → b%32≠23) ∧
  (a%64=33 → b%32≠23) ∧
  (a%64=5 → b%32≠20) ∧
  (a%16=3 → b%32≠18) ∧
  (a%32=9 → b%32≠9) ∧
  (a%64=21 → b%32≠20) ∧
  (a%16=9 → b%8≠5)

/-- Macro trace rows as (first counter, original total rank).
    Integer expressions avoid truncation in purely modular statements. -/
def rows (d : Digit) (X R : Int) : List (Int × Int) :=
  let start := (4*X-3,4*R-1)
  match d with
  | .zero => [start,(8*X-3,4*R+2),(16*X-3,4*R+5),(32*X-3,4*R+8),(64*X-3,4*R+11)]
  | .one => [start,(8*X-3,4*R+2),(16*X-3,4*R+5),(32*X-2*R-1,4*R+16),(64*X-4*R+1,4*R+19)]
  | .four => [start,(8*X-2*R-2,4*R+6),(16*X-4*R-1,4*R+9),(32*X-8*R+1,4*R+12),(64*X-16*R+5,4*R+15)]
  | .five => [start,(8*X-2*R-2,4*R+6),(16*X-4*R-1,4*R+9),(32*X-10*R+1,4*R+20),(64*X-20*R+5,4*R+23)]

def shiftedX (e : Digit) (X R : Int) : Int :=
  16*X+offset e-digit e*(R+cost e)

def shiftedR (e : Digit) (R : Int) : Int := R+cost e

def rowOK (s : Int × Int) : Prop := localFilters s.1 (s.2-2*s.1)

/-- The last three rows of every four-step macro satisfy all the listed
    filters automatically, irrespective of the initial residues. -/
theorem last_three_filters (d : Digit) (X R : Int) :
    ∀ s ∈ (rows d X R).drop 2, rowOK s := by
  intro s hs
  cases d <;> simp [rows] at hs <;>
    rcases hs with h|h|h <;> subst s <;>
    simp [rowOK,localFilters] <;> repeat' apply And.intro <;> omega

/-- Every row of the second macro satisfies the complete listed filter set.
    Thus an interior two-macro block already entails these tests. -/
theorem two_macro_filters (e d : Digit) (X R : Int) :
    ∀ s ∈ rows d (shiftedX e X R) (shiftedR e R), rowOK s := by
  intro s hs
  cases e <;> cases d <;>
    simp [rows,shiftedX,shiftedR,digit,cost,offset] at hs <;>
    rcases hs with h|h|h|h|h <;> subst s <;>
    simp [rowOK,localFilters] <;> repeat' apply And.intro <;> omega

#print axioms last_three_filters
#print axioms two_macro_filters
end BB429Q0Macro
