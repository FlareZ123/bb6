# Raw119 six-hole cylinder: complete candidate certificate

Parent 1RB---_1RC---_0RD---_1LD1RE_---0RE_------, E1=0RE, raw residual 119. The exhaustive TNF tree has 6,651 splits, 112,287 side cycles, 31,922 last-hole leaves and 8,765 formerly open leaves. Mass 25^6=244,140,625. Candidate exact weighted maximum 572, attained by 1RB0LF_1RC1RE_0RDHHH_1LD1RE_1LF0RE_1LA0LA (571 ordinary moves, halt, zero incoming delay).

A reusable bank of only 122 distinct DFA witnesses closes 8,746 of 8,765 open leaves by independently reconstructed FAR saturation. bank.cpp is an untrusted producer; the Lean FAR checker must accept the reconstructed masks. Nine counter leaves share one arbitrary-tail induction, nine other leaves have one-block sweep candidates and leaf 4028 has a two-block growth candidate E(0^(n+4)10100(100)^n) -> E(0^(n+5)10100(100)^(n+1)) in 66+8n steps, entry 56. 

Raw119Counter.lean is a universal proof for three table variants and arbitrary A1 transition: E(k,L,R) has left zipper 0^(6+k)10L. The mutually inductive countAdvance theorem computes clearing k zeros on the right and advancing through k+j bits on the left, preserving arbitrary untouched tails. It implies E(k,L,[]) -> E(k+1,L,[]) in positive time. The two base costs are 35/39; solving the cost recurrence gives (36 or 40)*2^k-1. The core growth proof and all nine entry/epoch/positive theorems compiled locally in Lean 4.36.0-rc2 against copied zipper primitives with propext/Quot.sound only. The source NeverHalts bridge uses the existing never_of_growth theorem. Full source audit and roster transfer are pending; no BB(6) upper bound claimed.


## Original-source audit status (2026-11-25)

The first `weighted-tnf-agent8-six` attempt (run 45577164247) reached the source-closure step but stopped before Lean compilation because the module index found two files named `Raw115Base` (Agent47's counter base and this project's generated raw115 base). The workflow now explicitly selects this project's intended module with:

```text
--override Raw115Base=im-results/agent8-tnf-six/raw115/Raw115Base.lean
```

The retry was dispatched as run 45581575103 and was in progress at 09:05Z. Do not treat raw115/raw119 as source-accepted until this retry compiles `SixSiblingRoster.lean` and passes the axiom gate.
