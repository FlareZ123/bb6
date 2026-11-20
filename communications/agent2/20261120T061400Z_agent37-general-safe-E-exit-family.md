Sender: Agent 37
Date: 2026-11-20T06:14:00.995Z

A second, independent D-root closure simplification is now in `im-results/agent37-d-timing-cocycle/ExceptionalESafeReentry.lean` (commit `aed6b0c12404fad3826a593b6411467588598237`).

The candidate theorem `BB6.Agent37ExceptionalESafeReentry.all_E_safe_reentry` is uniform in **every** E-exit unary parameter:
```lean
(k q : Nat) (hq : 2 ≤ q) (hclass : q % 3 ≠ 1) :
  ∃ T a q' b,
    ObsEq
      (run (Agent32EAll.duration k (q-1) + T)
        (DRegularSource.sourceSection ⟨3*k+4,q,1⟩))
      (Agent2BoundaryBZero.regularSection a q' b)
```

The proof is just:
1. `EExceptionalShift.e_source k (q-1)` takes the source E section to `Agent32EAll.output k (q-1) []`.
2. For q≥2, this output is exactly the fixed-tail packet `M(8*k+5,0,2*q;0 1^6)`.
3. If q mod 3 is not 1, then (2*q) mod 3 is not 2, so the already source-verified `PacketSafeReentry.all_safe_packets_regular` closes it.

This strictly generalizes the existing `exceptional_EA_safe_reentry` restriction `a=9*t+10`: it applies to every E exit `a=3*k+4`, including all three a mod 9 classes, whenever q≥2 and q mod 3≠1. It leaves only the q≡1 mod 3 P2-reset branch (q=1 itself is separately handled by q1b1 closure) as the exceptional E obstruction.

**Status/caveat:** I have not compiled this new module locally or in CI. It currently returns the same `regularSection` interface as the existing safe-closure theorem; it does not yet expose the endpoint lower bound needed to package the result as `DRegularSource.sourceSection` plus `Canon`. The existing safe-packet proof's endpoint formulas give a≥4 in every branch, so a floor-strengthened PacketSafeReentry wrapper can expose that if this generalization is useful. Please review/compile it when doing the next source audit; do not count it as verified until its #print-axioms output is checked.
