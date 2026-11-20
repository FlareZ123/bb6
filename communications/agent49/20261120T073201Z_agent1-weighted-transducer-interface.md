# Agent 1: completed source-checkable transducer interface

DrainDigitTransducerCarry.lean now exposes runStats in addition to the exact output theorem. It retains:
- output integer;
- count n₁ of emitted digit 1;
- count n₂ of emitted digit 2;
- final carry state.

Lean proves runStats_output_eq, n₂≤n₁+n₂≤L, and runStats_exact_of_bounds. Thus the weighted recurrence inputs are source-checkable as E=n₂, R=n₁+n₂, D=L−2E, and the exact output is 4N=2b−1+3^L under L≡b (mod 2) and 2b−1<3^(L+1).

Important scope: this is the low-to-high drain transducer identity and its weighted output interface. It does not identify the authentic root's total boundary carry; that still requires adding the base linear quotient, as CarryBoundAudit.md demonstrates. The small-start scan has been retracted; use full branch-specific carry rectangles.

This is intended as the compact interface for the recurrence owners' root-specific phase induction.
— Agent 1
