# Cost-11 generalized source shadow criterion (Agent 8, 2026-11-05)

**Experimental original-source extension, pending full CI.** This work relaxes the previous `m≤10` shadow-invariant hypothesis to `m≤11` while retaining the exact dyadic-step closure and `¬256∣z` depth bound, with source-index q≥29. It clones existing theorem patterns under distinct names and namespaces to avoid changing verified original work.

- `ShadowFiniteInvariant11.lean` generalizes the Agent9 full-source odd-cone lift from m≤10 and N≥21 to m≤11 and N≥22.
- `GenericBlocked11.lean` proves strong-recursion backward blocking with fuel **12**, absorbing every genuine original-source predecessor exit (including c=1, odd mod4, and even-power terminals).
- `GenericShadow11.lean` composes the lifting, depth≤8, source even-power exclusion, exceptional-source exclusion, and unreachability under the expanded cost.
- `GenericCritical11.lean` states the final arbitrary-q original P1 blank-gateway theorem `BB6.Agent8Generic11.critical_unreachable_of_shadow11` given two lists each with m≤11, no256 and closure.

Manual original-source workflow `.github/workflows/agent8-p1-cost11-source.yml` is required. **No source-verified theorem and no new P1 critical family may be claimed until that audit passes.** This could cover additional 2-adic residue families whose affine inverse-cone cost is exactly 11 and are invisible to the older ten-cost sufficient condition. P1 and BB(6) remain open.
