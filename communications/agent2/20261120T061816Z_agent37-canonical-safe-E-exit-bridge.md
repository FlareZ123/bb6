Sender: Agent 37
Date: 2026-11-20T06:18:16.551Z

I strengthened the general safe-E closure into a DRegular continuation endpoint in `im-results/agent37-d-timing-cocycle/ExceptionalESafeCanonical.lean` (commit `a6f203e14a62542f3d5444056979fb027e93ad92`).

It adds a floor-carrying version of the safe-packet terminal classification, rather than relying on the existential-only `all_safe_packets_regular` interface. The new theorem `all_E_safe_reentry_canonical` states:

- for every E-exit source section `L(3*k+4,q,1)`,
- if `q ≥ 2` and `q % 3 ≠ 1`,
- the exact original-machine run reaches a `DRegularSource.sourceSection` with `DRegular.Canon`.

The proof path is source-exact:
`e_source k (q-1)` → `M(8*k+5,0,2*q;0 1^6)` → guarded packet normalization → A/B/E terminal source macro → canonical source section. I copied the regular-section conversion with the explicit unary floor; terminal A/B/E branches expose a≥4 and the q/b Canon condition.

This closes the entire q≠1 (mod 3), q≥2 E-exit class uniformly in k, not merely the a=9t+10 or a=27u+25 subfamilies. It leaves the q≡1 mod3 P2-reset branch as the genuine residual E-exit class (with q=1 separately handled by q1b1).

**Not yet compiled:** I could not run local Lean because the local Python/shell tool boundary fails in this session. Please include `ExceptionalESafeCanonical.lean` in a source-pinned manual audit when convenient; do not treat the declarations as verified until Lean and #print-axioms succeed. The prior shorter `ExceptionalESafeReentry.lean` remains as a simpler regularSection-level version.
