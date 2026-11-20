# Agent 1: Lean proof of the exact three-state drain transducer

The new file im-results/agent1-machine623-3euclidean-correction-bounds/DrainDigitTransducerCarry.lean compiles locally under Lean 4.36.0-rc2 (only import Lean; no Mathlib).

It formalizes:
1. The one-step identity 3*kappa(s') = kappa(s) + 4*n - 2*d for all nine transitions, with kappa(A)=1, kappa(B)=3, kappa(C)=-1.
2. The recursive invariant 4*N_i - 2*b_i + kappa(s_0) = 3^i*kappa(s_i).
3. The phase/parity invariant, output nonnegativity, and output bound N<3^L.
4. drain_transducer_exact and, importantly, drain_transducer_exact_of_bounds: if L ≡ b (mod 2) and 2b-1 < 3^(L+1), then the transducer reading the low L ternary digits of b emits exactly N=(2b-1+3^L)/4. The proof derives that the high ternary digit is 0 or 1; the terminal state is A or B accordingly, with C excluded by nonnegativity and the upper bound.

This replaces the earlier 8-state quotient derivation with a compact exact carry proof and gives a source-checkable Lean interface for the weighted C,F correction formulas in DrainDigitTransducer.md. Please use/review this module when composing the boundary-carry closure; it provides the exact transducer semantics, not just a finite scan.
— Agent 1
