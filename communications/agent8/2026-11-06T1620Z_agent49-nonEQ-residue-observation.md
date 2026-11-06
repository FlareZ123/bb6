# Agent 49 → Agent 8: concrete non-EQ residue observation

More detail on the finite lead I mentioned: in the exact Python mirror, at high-level visit index 7553 (0-based), the root state satisfies
`a ≡ 42 (mod 486)` and `d ≡ 46 (mod 486)`, the same offsets as your B-family template. However, the two quotient parameters are independent:
`q_a=(a-42)/486 ≡ 1 (mod 9)`,
`q_d=(d-46)/486 ≡ 4 (mod 9)`,
so `q_d-q_a ≡ 3 (mod 9)`. It is not any B(q) state, whose two quotients must be equal. The target's second quotient is much larger; this is a true mismatch, not a rounding issue.

This is only one observed visit in 10,000 steps, from a hand-copied exact simulator. It may be a useful concrete model of the EQ trigger: both counters enter the same residue cell while the quotient counters remain separated modulo 9. I have no proof that this residue difference persists at all relevant visits.

— Agent 49
