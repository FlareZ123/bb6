# Exactness of the P1 critical carry prefix

**2026-11-24 — Lean checked against the original inverse-cone definitions.** This is a structural result about the critical inverse root, not a decision of the P1 blank orbit.

## Theorem

Let n >= 14, 1 <= K <= n. For any Boolean word x_0,...,x_{K-1}, with x_0=1, suppose

    sum_{j<K} x_j (n+j+3) 2^j = 1 (mod 2^K).

Then there is an actual OddCone history from (14*2^n-2*n-16,3) of total inverse cost exactly K. The endpoint is not prescribed. See P1CarryExactSource.lean, theorem source_prefix_to_oddcone. The converse necessity for a history of cost at least K is the existing endpoint-independent cost witness and prefix bridge of Agents 43/50 (WallListSource.lean and WallPrefixListBridge.lean). Consequently, on this interval, the prefix-existence question is exact, including existence of a source history reaching cost at least K. There is no extra generic first-edge guard that can remove surviving prefixes in this domain. Endpoint-specific conditions can still exclude a target.

## Proof mechanism

Put T=7*2^n, v=(d-1)/2, w=(b+12)/2. The source mass is v+w+n+m+1=T, where m is accumulated cost. At the root v=1, w=T-n-2. A legal source edge of cost e=t+1 satisfies

    v+T = 2^e v' + (n+m+3).

The parent guards are w>=10 and w even; the child guards are v'>=2 and w'>=6. The mass and dyadic equation give the original inverseAt equation with t=e-1, k=w'-4, c=2v'-3, by inverseAt_iff_power_mass.

Split an edge into a selected bit followed by e-1 unselected bits. At each unit-cost position m the exact two-coordinate transitions are

    one:  v+T = 2v'+n+m+3, w=2w'
    zero: v=2v', w+T=2w'+n+m+3.

The first bit must be one. A zero extends the preceding gap (does not create a new source edge). Mass is preserved. Both coordinates are at least (T-n-2)/2^m after the leading one. For m<=n both are at least 7; for m<n the left shifted coordinate w is at least 14. Hence all source size guards are automatic in the interval, and the selected bit's integrality supplies w even.

The small positive carry c begins at (n+2)/2 after the first bit and evolves by

    c+x_m(n+m+3) = 2c'.

The exact coordinate and carry satisfy 2^(n-m) | v+c. Below n this makes the selected and unselected transitions integral at exactly the required parity; it is preserved because v'+c'=(v+c+x_m*T)/2. A valid weighted modular word supplies the successive integral carries by division, and hence a legal microtrace of length K. Grouping each one and its following zeros proves the LegalGap relation, which is then mapped into actual source OddCone constructors.

## Reproduction

Lean 4.36.0-rc2: compile P1CarryExact.lean, then P1CarryExactSource.lean using the existing modules. The local check compiled the exact seven dependency blobs from repository commit 2a30d3def3431627fa9412d5029fe2822e980325 in this order:

- GParity: 83ab5fbe1b23c14a8155283b0f203e83236d1fb9
- GInverse: f820b28010ca4b7d7ed4dc5af8e6fcb08d1b7b6d
- P1FiniteInverse: 2f1963348c7534f1875bf48e002a19dd0c33704f
- MassInverse: df9da9999fa4d9fcb2bcf1642c41ddf3f37aceae
- P1InverseLog: c91b15b24e7de855233fd4a58ab72293e21d9c79
- InverseIff: c4e3390594470ac6ad6467238a58f20adfd79f8a
- OddConeMass: 35337a3f6fa533cf2b827133c3c8a1e5ab6b44e1

All were compiled locally with lean -o MODULE.olean MODULE.lean and LEAN_PATH set to the module directory. Both source theorems print only [propext, Classical.choice, Quot.sound]; no sorryAx. The two new proof blobs are 5d6be4ba7bb498c84792e64a6af43889faa4c0c2 and 4edcd086e2183ff67e225ff95eeccf5aca3255a9.

## Implications and limits

The previous carry sieve is a lossless decision for the existence of any inverse history of cost K<=n, not just a relaxation. A surviving prefix need not lead to the right-five endpoint or either restart state; nor does it establish that the critical root is on the authentic blank orbit. Beyond n the divisibility and automatic-size argument no longer applies as stated. Progress on surviving parameters must exploit endpoint-specific restrictions, a stronger arithmetic bound on the length-n prefix, or exact post-cutoff dynamics. Do not infer P1 nonhalting or a BB(6) upper bound.
