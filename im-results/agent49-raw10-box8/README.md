# Raw10 original box 8: complete finite/symbolic closure

## Scope
The original base34 rectangle is index 8 (zero based), fixed transition codes
`[8,14,11,7,17,4,9,2,23,15]`. Its F0 domain is all 25 codes
except 16 (the q2800 held cylinder was already removed), and F1 is unrestricted.
It therefore contains 600 completions. Code 0 means an assigned halt,
not an absent transition.

## Exact classification
* F0=0: all 25 F1 choices halt after 10 live steps.
* F0=12,22,24 with F1=0: halt after 32,11,11 live steps respectively.
  With an ordinary F1 these are total ordinary-transition machines, so never halt.
* F0=1,14: symbolic sweeping growth, independent of F1.
* The other 18 permitted F0 choices: exact finite retained-half-line translated
  cycles, independent of F1, including the previously known exact cycle at 10.

This partitions the rectangle into 28 halting and 572 nonhalting completions.
Maximum ordinary score is 33 (including the final halt). Allowing up to five
initial blank-delay steps gives the conservative weighted bound 38.

## Symbolic progress
Let F(n) be state F scanning a zero, blank left ray, right tape
`(100)^n1` then blanks. From the blank start F(1) is reached after ten
live transitions. For every natural n:
* F0=0LA: F(n) -> F(n+2) in 8n+19 live steps.
* F0=0RD: F(n) -> F(n+1) in 8n+12 live steps.

The exact ray identities are in Box8Sweep.lean. The A-state forward
triplet sweep takes five steps per block, the D-state backward triplet
sweep takes three, and the two boundary segments take seven and three.
Positive-length iteration proves every finite prefix exists, so no
choice of F1 can cause a halt.

## Proof status
Box8Sweep.lean compiled locally under Lean 4.36.0-rc2 against the exact
extracted primitive ray definitions, with only propext and Quot.sound.
Box8Closure.lean combines the original source-index bridge, the sweep
transfer theorem, 18 finite-cycle checks, four finite halt checks and an
exhaustive Fin 25 partition. The full source-closure workflow target
`weighted-tnf-raw10-box8-complete` has been dispatched; do not treat its
result as accepted until it succeeds. Local git checkout was unavailable
due to DNS resolution failure.

The exported `residual_without_box8` consumer uses finite domain-subset
matching instead of requiring a stable index in later split rectangles.
It can be applied to any residual list with the weighted predicate at
bound B >= 38. The number of eliminated entries in a particular
combined roster must still be computed, not inferred from the original
index.

This is a partial Raw10 closure, not an upper bound for BB(6).
