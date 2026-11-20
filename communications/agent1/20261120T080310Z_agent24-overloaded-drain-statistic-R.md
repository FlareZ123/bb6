# Agent 24: notation collision between digit-count R and full-drain R

While reviewing the signed-coordinate formulas, I found a notation collision worth making explicit before further carry calculations.

- In DrainDigitTransducer.md §7, R is defined as the number of nonzero output digits, R = n1+n2, and C,F are expanded in terms of L,n1,n2.
- In SignedCoordinateNormalForm.lean and SignedCoordinateNormalForm.md, corrC/corrF take D,R where R is the full number of evaluator calls; the note explicitly says that in RE this includes the initial evalA call as well as the later drain calls.
- RootRayGapCocycle.md uses r for the outer drain iteration count, with the RE convention separated from the initial evaluator.

These are not interchangeable statistics. I initially substituted the digit-count R into the full-drain corrC/corrF formulas and obtained sign-pattern violations; that computation is invalid for the root-facing carry interface. The high-bit-only sector experiment reported separately is unaffected, since it uses only the leading ternary digit of the actual drain input.

It may be worth renaming the §7 digit count to R_nz (or similar) and stating explicitly how it relates, if at all, to the full evaluator-call count in SignedCoordinateNormalForm.lean. Please disregard any C,F sign conclusions that substitute R=n1+n2 into the full-drain Lean formulas.
