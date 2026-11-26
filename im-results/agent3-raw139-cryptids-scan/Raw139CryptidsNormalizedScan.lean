/-
Exact table matcher for the 34 BB(6) NonHalt modules in
google-deepmind/cryptids@3647718b5df22e1a61462dec0376bd204526285a.
This checks the actual Raw139Normalized p0, acceptedRows, and remainingRows
definitions. It does not import the upstream source proofs and does not claim
that a compatible one-hole leaf alone covers its whole residual cylinder.
-/
import Raw139Normalized
import HardRootCore

namespace BB6.Agent3Raw139CryptidsScan

open BB6Coverage
open BB6.Agent19HardRoot
open BB6.Agent6Raw139Normalized

/-- Pinned upstream RLE inventory; entries are literal transition tables. -/
def candidates : List (String × Machine) := [
  ("1RB0LD_1RC0RE_1LD0RE_1LA0LA_1RB1RF_1RBHHH", literal [some ⟨true, true, 1⟩, some ⟨false, false, 3⟩, some ⟨true, true, 2⟩, some ⟨false, true, 4⟩, some ⟨true, false, 3⟩, some ⟨false, true, 4⟩, some ⟨true, false, 0⟩, some ⟨false, false, 0⟩, some ⟨true, true, 1⟩, some ⟨true, true, 5⟩, some ⟨true, true, 1⟩, none]),
  ("1RB0LE_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LDHHH", literal [some ⟨true, true, 1⟩, some ⟨false, false, 4⟩, some ⟨true, true, 2⟩, some ⟨false, true, 2⟩, some ⟨true, false, 3⟩, some ⟨false, true, 1⟩, some ⟨true, false, 0⟩, some ⟨false, false, 4⟩, some ⟨true, false, 3⟩, some ⟨true, false, 5⟩, some ⟨true, false, 3⟩, none]),
  ("1RB0LE_1RC1LA_1LD1RE_1LB0LD_1RF0RC_1RBHHH", literal [some ⟨true, true, 1⟩, some ⟨false, false, 4⟩, some ⟨true, true, 2⟩, some ⟨true, false, 0⟩, some ⟨true, false, 3⟩, some ⟨true, true, 4⟩, some ⟨true, false, 1⟩, some ⟨false, false, 3⟩, some ⟨true, true, 5⟩, some ⟨false, true, 2⟩, some ⟨true, true, 1⟩, none]),
  ("1RB0RA_1RC0LE_1LD0RA_HHH1LE_0RE0LF_1LB1LC", literal [some ⟨true, true, 1⟩, some ⟨false, true, 0⟩, some ⟨true, true, 2⟩, some ⟨false, false, 4⟩, some ⟨true, false, 3⟩, some ⟨false, true, 0⟩, none, some ⟨true, false, 4⟩, some ⟨false, true, 4⟩, some ⟨false, false, 5⟩, some ⟨true, false, 1⟩, some ⟨true, false, 2⟩]),
  ("1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC1LF_0LCHHH", literal [some ⟨true, true, 1⟩, some ⟨false, true, 0⟩, some ⟨true, true, 2⟩, some ⟨false, true, 2⟩, some ⟨true, false, 3⟩, some ⟨false, false, 4⟩, some ⟨true, true, 0⟩, some ⟨true, false, 2⟩, some ⟨true, false, 2⟩, some ⟨true, false, 5⟩, some ⟨false, false, 2⟩, none]),
  ("1RB0RA_1RC0RC_1LD1RF_HHH1LE_1RF0LF_1RA0LE", literal [some ⟨true, true, 1⟩, some ⟨false, true, 0⟩, some ⟨true, true, 2⟩, some ⟨false, true, 2⟩, some ⟨true, false, 3⟩, some ⟨true, true, 5⟩, none, some ⟨true, false, 4⟩, some ⟨true, true, 5⟩, some ⟨false, false, 5⟩, some ⟨true, true, 0⟩, some ⟨false, false, 4⟩]),
  ("1RB0RA_1RC0RD_1LD1LE_1LF0LC_0LDHHH_1RA1LD", literal [some ⟨true, true, 1⟩, some ⟨false, true, 0⟩, some ⟨true, true, 2⟩, some ⟨false, true, 3⟩, some ⟨true, false, 3⟩, some ⟨true, false, 4⟩, some ⟨true, false, 5⟩, some ⟨false, false, 2⟩, some ⟨false, false, 3⟩, none, some ⟨true, true, 0⟩, some ⟨true, false, 3⟩]),
  ("1RB0RD_1RC1RF_1LD0LE_1RA0LC_1RE1LC_0RAHHH", literal [some ⟨true, true, 1⟩, some ⟨false, true, 3⟩, some ⟨true, true, 2⟩, some ⟨true, true, 5⟩, some ⟨true, false, 3⟩, some ⟨false, false, 4⟩, some ⟨true, true, 0⟩, some ⟨false, false, 2⟩, some ⟨true, true, 4⟩, some ⟨true, false, 2⟩, some ⟨false, true, 0⟩, none]),
  ("1RB0RD_1RCHHH_1LD1LC_1LE0LC_1RF0RC_1RA0RF", literal [some ⟨true, true, 1⟩, some ⟨false, true, 3⟩, some ⟨true, true, 2⟩, none, some ⟨true, false, 3⟩, some ⟨true, false, 2⟩, some ⟨true, false, 4⟩, some ⟨false, false, 2⟩, some ⟨true, true, 5⟩, some ⟨false, true, 2⟩, some ⟨true, true, 0⟩, some ⟨false, true, 5⟩]),
  ("1RB0RD_1RCHHH_1LD1LE_1LE0LC_1RF1LD_1RA0RF", literal [some ⟨true, true, 1⟩, some ⟨false, true, 3⟩, some ⟨true, true, 2⟩, none, some ⟨true, false, 3⟩, some ⟨true, false, 4⟩, some ⟨true, false, 4⟩, some ⟨false, false, 2⟩, some ⟨true, true, 5⟩, some ⟨true, false, 3⟩, some ⟨true, true, 0⟩, some ⟨false, true, 5⟩]),
  ("1RB0RE_1RC1RE_1LD1RA_1LA0LD_0RA0LF_1LDHHH", literal [some ⟨true, true, 1⟩, some ⟨false, true, 4⟩, some ⟨true, true, 2⟩, some ⟨true, true, 4⟩, some ⟨true, false, 3⟩, some ⟨true, true, 0⟩, some ⟨true, false, 0⟩, some ⟨false, false, 3⟩, some ⟨false, true, 0⟩, some ⟨false, false, 5⟩, some ⟨true, false, 3⟩, none]),
  ("1RB0RF_1RC0RB_1LD0RA_1LE0LD_1RB0LC_1LAHHH", literal [some ⟨true, true, 1⟩, some ⟨false, true, 5⟩, some ⟨true, true, 2⟩, some ⟨false, true, 1⟩, some ⟨true, false, 3⟩, some ⟨false, true, 0⟩, some ⟨true, false, 4⟩, some ⟨false, false, 3⟩, some ⟨true, true, 1⟩, some ⟨false, false, 2⟩, some ⟨true, false, 0⟩, none]),
  ("1RB0RF_1RC0RE_1LD1RA_1LA0LD_1RAHHH_0RA0LB", literal [some ⟨true, true, 1⟩, some ⟨false, true, 5⟩, some ⟨true, true, 2⟩, some ⟨false, true, 4⟩, some ⟨true, false, 3⟩, some ⟨true, true, 0⟩, some ⟨true, false, 0⟩, some ⟨false, false, 3⟩, some ⟨true, true, 0⟩, none, some ⟨false, true, 0⟩, some ⟨false, false, 1⟩]),
  ("1RB0RF_1RC0RE_1LD1RA_1LA0LD_1RAHHH_0RE0LB", literal [some ⟨true, true, 1⟩, some ⟨false, true, 5⟩, some ⟨true, true, 2⟩, some ⟨false, true, 4⟩, some ⟨true, false, 3⟩, some ⟨true, true, 0⟩, some ⟨true, false, 0⟩, some ⟨false, false, 3⟩, some ⟨true, true, 0⟩, none, some ⟨false, true, 4⟩, some ⟨false, false, 1⟩]),
  ("1RB0RF_1RC1RF_1LD0RE_HHH0LE_1LA0LE_0RA0LC", literal [some ⟨true, true, 1⟩, some ⟨false, true, 5⟩, some ⟨true, true, 2⟩, some ⟨true, true, 5⟩, some ⟨true, false, 3⟩, some ⟨false, true, 4⟩, none, some ⟨false, false, 4⟩, some ⟨true, false, 0⟩, some ⟨false, false, 4⟩, some ⟨false, true, 0⟩, some ⟨false, false, 2⟩]),
  ("1RB0RF_1RC1RF_1LD1RA_HHH0LE_1LA0LE_0RA0LC", literal [some ⟨true, true, 1⟩, some ⟨false, true, 5⟩, some ⟨true, true, 2⟩, some ⟨true, true, 5⟩, some ⟨true, false, 3⟩, some ⟨true, true, 0⟩, none, some ⟨false, false, 4⟩, some ⟨true, false, 0⟩, some ⟨false, false, 4⟩, some ⟨false, true, 0⟩, some ⟨false, false, 2⟩]),
  ("1RB1LB_1RC0LA_1LD1RF_1RB0LE_HHH1LA_1RD0RD", literal [some ⟨true, true, 1⟩, some ⟨true, false, 1⟩, some ⟨true, true, 2⟩, some ⟨false, false, 0⟩, some ⟨true, false, 3⟩, some ⟨true, true, 5⟩, some ⟨true, true, 1⟩, some ⟨false, false, 4⟩, none, some ⟨true, false, 0⟩, some ⟨true, true, 3⟩, some ⟨false, true, 3⟩]),
  ("1RB1LC_1RC1LB_1LD0RB_0LE1RD_HHH0LF_0LA1LF", literal [some ⟨true, true, 1⟩, some ⟨true, false, 2⟩, some ⟨true, true, 2⟩, some ⟨true, false, 1⟩, some ⟨true, false, 3⟩, some ⟨false, true, 1⟩, some ⟨false, false, 4⟩, some ⟨true, true, 3⟩, none, some ⟨false, false, 5⟩, some ⟨false, false, 0⟩, some ⟨true, false, 5⟩]),
  ("1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD0LF_1RDHHH", literal [some ⟨true, true, 1⟩, some ⟨true, false, 3⟩, some ⟨true, true, 2⟩, some ⟨false, true, 1⟩, some ⟨true, false, 3⟩, some ⟨false, true, 3⟩, some ⟨true, false, 0⟩, some ⟨false, false, 4⟩, some ⟨true, false, 3⟩, some ⟨false, false, 5⟩, some ⟨true, true, 3⟩, none]),
  ("1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_0LDHHH", literal [some ⟨true, true, 1⟩, some ⟨true, false, 3⟩, some ⟨true, true, 2⟩, some ⟨false, true, 1⟩, some ⟨true, false, 3⟩, some ⟨false, true, 3⟩, some ⟨true, false, 0⟩, some ⟨false, false, 4⟩, some ⟨true, false, 3⟩, some ⟨true, false, 5⟩, some ⟨false, false, 3⟩, none]),
  ("1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_1LAHHH", literal [some ⟨true, true, 1⟩, some ⟨true, false, 3⟩, some ⟨true, true, 2⟩, some ⟨false, true, 1⟩, some ⟨true, false, 3⟩, some ⟨false, true, 3⟩, some ⟨true, false, 0⟩, some ⟨false, false, 4⟩, some ⟨true, false, 3⟩, some ⟨true, false, 5⟩, some ⟨true, false, 0⟩, none]),
  ("1RB1RA_1RC0RA_1LD0LA_1LE0LD_1LF0LB_1REHHH", literal [some ⟨true, true, 1⟩, some ⟨true, true, 0⟩, some ⟨true, true, 2⟩, some ⟨false, true, 0⟩, some ⟨true, false, 3⟩, some ⟨false, false, 0⟩, some ⟨true, false, 4⟩, some ⟨false, false, 3⟩, some ⟨true, false, 5⟩, some ⟨false, false, 1⟩, some ⟨true, true, 4⟩, none]),
  ("1RB1RA_1RC0RA_1LD1RB_1LE0LD_1LF0LB_1LAHHH", literal [some ⟨true, true, 1⟩, some ⟨true, true, 0⟩, some ⟨true, true, 2⟩, some ⟨false, true, 0⟩, some ⟨true, false, 3⟩, some ⟨true, true, 1⟩, some ⟨true, false, 4⟩, some ⟨false, false, 3⟩, some ⟨true, false, 5⟩, some ⟨false, false, 1⟩, some ⟨true, false, 0⟩, none]),
  ("1RB1RA_1RC1LB_1LD0RA_1LA0LE_HHH0LF_0RC0LB", literal [some ⟨true, true, 1⟩, some ⟨true, true, 0⟩, some ⟨true, true, 2⟩, some ⟨true, false, 1⟩, some ⟨true, false, 3⟩, some ⟨false, true, 0⟩, some ⟨true, false, 0⟩, some ⟨false, false, 4⟩, none, some ⟨false, false, 5⟩, some ⟨false, true, 2⟩, some ⟨false, false, 1⟩]),
  ("1RB1RC_1RC0RA_1LD1RB_1LE0LD_1LF0LB_1LAHHH", literal [some ⟨true, true, 1⟩, some ⟨true, true, 2⟩, some ⟨true, true, 2⟩, some ⟨false, true, 0⟩, some ⟨true, false, 3⟩, some ⟨true, true, 1⟩, some ⟨true, false, 4⟩, some ⟨false, false, 3⟩, some ⟨true, false, 5⟩, some ⟨false, false, 1⟩, some ⟨true, false, 0⟩, none]),
  ("1RB1RF_1RC0RA_1LD1RB_1LE0LD_1LA0LB_0RBHHH", literal [some ⟨true, true, 1⟩, some ⟨true, true, 5⟩, some ⟨true, true, 2⟩, some ⟨false, true, 0⟩, some ⟨true, false, 3⟩, some ⟨true, true, 1⟩, some ⟨true, false, 4⟩, some ⟨false, false, 3⟩, some ⟨true, false, 0⟩, some ⟨false, false, 1⟩, some ⟨false, true, 1⟩, none]),
  ("1RB1RF_1RC0RA_1LD1RB_1LE0LD_1LB0LB_0RBHHH", literal [some ⟨true, true, 1⟩, some ⟨true, true, 5⟩, some ⟨true, true, 2⟩, some ⟨false, true, 0⟩, some ⟨true, false, 3⟩, some ⟨true, true, 1⟩, some ⟨true, false, 4⟩, some ⟨false, false, 3⟩, some ⟨true, false, 1⟩, some ⟨false, false, 1⟩, some ⟨false, true, 1⟩, none]),
  ("1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_0RBHHH", literal [some ⟨true, true, 1⟩, some ⟨true, true, 5⟩, some ⟨true, true, 2⟩, some ⟨false, true, 0⟩, some ⟨true, false, 3⟩, some ⟨true, true, 1⟩, some ⟨true, false, 4⟩, some ⟨false, false, 3⟩, some ⟨true, true, 1⟩, some ⟨false, false, 1⟩, some ⟨false, true, 1⟩, none]),
  ("1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_1RAHHH", literal [some ⟨true, true, 1⟩, some ⟨true, true, 5⟩, some ⟨true, true, 2⟩, some ⟨false, true, 0⟩, some ⟨true, false, 3⟩, some ⟨true, true, 1⟩, some ⟨true, false, 4⟩, some ⟨false, false, 3⟩, some ⟨true, true, 1⟩, some ⟨false, false, 1⟩, some ⟨true, true, 0⟩, none]),
  ("1RB1RF_1RC0RA_1LD1RB_1LE0LD_1RB0LB_1REHHH", literal [some ⟨true, true, 1⟩, some ⟨true, true, 5⟩, some ⟨true, true, 2⟩, some ⟨false, true, 0⟩, some ⟨true, false, 3⟩, some ⟨true, true, 1⟩, some ⟨true, false, 4⟩, some ⟨false, false, 3⟩, some ⟨true, true, 1⟩, some ⟨false, false, 1⟩, some ⟨true, true, 4⟩, none]),
  ("1RB1RF_1RC1RA_1LD0LA_HHH0LE_0LF1LE_0RA0LC", literal [some ⟨true, true, 1⟩, some ⟨true, true, 5⟩, some ⟨true, true, 2⟩, some ⟨true, true, 0⟩, some ⟨true, false, 3⟩, some ⟨false, false, 0⟩, none, some ⟨false, false, 4⟩, some ⟨false, false, 5⟩, some ⟨true, false, 4⟩, some ⟨false, true, 0⟩, some ⟨false, false, 2⟩]),
  ("1RBHHH_1RC0RF_1LD1RB_1LE0LD_1RB0LB_1RB1RA", literal [some ⟨true, true, 1⟩, none, some ⟨true, true, 2⟩, some ⟨false, true, 5⟩, some ⟨true, false, 3⟩, some ⟨true, true, 1⟩, some ⟨true, false, 4⟩, some ⟨false, false, 3⟩, some ⟨true, true, 1⟩, some ⟨false, false, 1⟩, some ⟨true, true, 1⟩, some ⟨true, true, 0⟩]),
  ("1RBHHH_1RC1LF_1LD1RE_1LB0LD_1RA0RC_1RC0LE", literal [some ⟨true, true, 1⟩, none, some ⟨true, true, 2⟩, some ⟨true, false, 5⟩, some ⟨true, false, 3⟩, some ⟨true, true, 4⟩, some ⟨true, false, 1⟩, some ⟨false, false, 3⟩, some ⟨true, true, 0⟩, some ⟨false, true, 2⟩, some ⟨true, true, 2⟩, some ⟨false, false, 4⟩]),
  ("1RBHHH_1RC1RE_1LD0RC_0RE0LD_1LC0LF_1RA0RF", literal [some ⟨true, true, 1⟩, none, some ⟨true, true, 2⟩, some ⟨true, true, 4⟩, some ⟨true, false, 3⟩, some ⟨false, true, 2⟩, some ⟨false, true, 4⟩, some ⟨false, false, 3⟩, some ⟨true, false, 2⟩, some ⟨false, false, 5⟩, some ⟨true, true, 0⟩, some ⟨false, true, 5⟩])
]

def address (r : Fin 7 × Move) : Nat × Bool × Bool × Nat :=
  (r.1.val, r.2.write, r.2.right, r.2.next.val)

def samePartial (p q : PartialMachine) : Bool :=
  allSlots.all fun s => decide (p s = q s)

/-- For each source table, report root compatibility, exact accepted-parent
    matches, compatible normalized residual rows, and exact one-hole matches. -/
def scanOne (c : String × Machine) :
    String × Bool × List (Nat × Bool × Bool × Nat) ×
      List (Nat × Bool × Bool × Nat) × List (Nat × Bool × Bool × Nat) :=
  let accepted := acceptedRows.filter (fun r => parentCheck (child r.1 r.2) c.2)
  let remaining := remainingRows.filter (fun r => parentCheck (leaf r) c.2)
  let exactLeaves := remainingRows.filter (fun r =>
    samePartial (leaf r) (BB6.Agent47WeightedHalt.forgetHaltRows c.2))
  (c.1, parentCheck p0 c.2, accepted.map address, remaining.map address, exactLeaves.map address)

def scan := candidates.map scanOne

theorem candidate_count : candidates.length = 34 := by decide

#eval (acceptedRows.length, remainingRows.length, candidates.length)
#eval scan

end BB6.Agent3Raw139CryptidsScan
