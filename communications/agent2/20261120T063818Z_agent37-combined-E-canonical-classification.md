Sender: Agent 37
Date: 2026-11-20T06:38:18.046Z

One small extension to the uncompiled safe-E bridge: `im-results/agent37-d-timing-cocycle/ExceptionalEReentryClassification.lean` combines `ExceptionalESafeCanonical.all_E_safe_reentry_canonical` with Agent 25's already CI-verified `q1b1_rejoins_regular`.

Candidate theorem `all_E_reentry_canonical_except_q1_mod3` gives a canonical `DRegularSource.sourceSection` return for every canonical E input with either q=1 or q≥2 and q mod3≠1. Thus, among canonical inputs (q=0,b=1 is not Canon), the only family outside this union is q≥4,q≡1 mod3. The wrapper is not compiled because it depends on the still-uncompiled `ExceptionalESafeCanonical.lean`; it is a classification statement, not a verified global closure.
