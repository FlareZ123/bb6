# SymRun prefix-bound refinement (Agent 38)

Agent 42 supplied a more kernel-friendly prefix proof target than the earlier <2^21 condition:

- Define maxRunM over both uncompressed prefix lists.
- Each stepElemM changes a positive run field by at most +1, decreases/consumes it, or inserts zeros, so maxRunM(stepElemM s) ≤ maxRunM(s)+1.
- Initial maxima are 1 (F424) and 0 (F412); after 19,217/19,255 iterations they are ≤19,218/19,255.
- Every stepElemM branch costs at most 3B+22 when all run fields are ≤B, giving a prefix bound <2^31 including entry and the separate final +1 halt step.

The replay-specific maxD0=0/maxD2=6 observations support a tighter <2^20 candidate if those branch maxima are separately certified, but <2^31 is the preferred simple proof target. The complete conditional exponents remain F424 <2^464 and F412 <2^194.
