# TM63 complete 24-class source-dispatcher probe

Date: 2026-11-21

This probe checks the complete one-step source-dispatch recurrence against the actual TM2 transition table and S1 tape encoding, step by step. It is not a Lean proof and does not establish the arbitrary-parameter theorem.

## Tested parameter grid

The inline JavaScript runtime reproduction passed **48 cases**:
- initial index (n_0\in\{24,48\});
- initial marker (m_0\in\{0,1,2\});
- initial left exponent (a_0\in\{1,2\});
- initial right counter (b_0\in\{0,1\});
- tape width (L\in\{8,16\}).

Each run executes all (n_0) decrements, checking the exact complete nonblank tape support, state, and head after every proposed source increment. The runs cover all **24** pairs
[
(n\bmod 8,m\bmod 3)\in\{0,\ldots,7\}\times\{0,1,2\}.
]
The 48 runs simulate **1,086,624** primitive transitions in total.

The checked one-step arithmetic is:
[
m'=(m+2)\bmod3,\qquad
a'=a+b+\begin{cases}1&m\equiv0\pmod3,\\2&\text{otherwise},\end{cases}
\qquad b'=2^b-1,
]
with proposed cost
[
6\cdot4^b+42\cdot2^b+15+4(m\bmod3)+12(a+v_2(n))-9b
]
and head displacement (5+3b). At every step the simulated tape exactly matched
[
S1(L,n-1,m',a',0,b',h+5+3b).
]
The terminal configuration also matched the recursively computed `sectionResult` record, including total cost, marker, exponent, right counter, and head.

## Exact-integer requirement

An initial Number-based exploratory harness appeared to fail in the marker-2, residue-5 class once the evolving exponent reached 54. This was a simulator bug: JavaScript `Number` cannot represent (2^{55}-1) exactly. Replacing the binary decoder with BigInt arithmetic removed the discrepancy, and the full 48-case grid passed. The committed [`TM63SourceDispatcherProbe.mjs`](TM63SourceDispatcherProbe.mjs) uses BigInt throughout binary decoding; do not weaken it to Number.

## Interpretation and limitation

This is a finite integration check of all 24 dispatch classes, including the M0/M2 residue-zero families and the all-valuation M1 family. It supports the consistency of the source recurrence for small counters and evolving exponents. It does **not** prove the generic Lean source theorems, validate their transitive axiom profiles, or close the authentic-root composition. Exact RC2 compilation and `#print axioms` remain mandatory.
