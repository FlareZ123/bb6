# Product obstruction at grouped nonblank B returns — definitive counterexample

Supersedes only the open possibility in RunSection.md's final paragraph (the exact run map and all-B obstruction there remain valid).

**Theorem (paper-level, finite exact witness):** no single Cartesian-product invariant X × Y on the left run word and shortened right W at *nonblank* B section boundaries can contain the initial B state, be closed under the exact nonblank-B return, and avoid fatal. This also rules out the proposed grouped product-language fixed point, even if X and Y are arbitrary infinite/nonregular languages. It is not a statement that F197 halts from blank.

Use L inclusive left, W with B full right 00W (shortened tail 0W), nearest-first bit strings trimmed of trailing zeros. Initial B section (11,1). The nonblank return is one B episode, D scan if it exits, and continue through any blank-left B episode until a nonblank B entry or fatal. All rows below have nonblank left inputs and outputs. At every row the two input components separately occurred in initial seed or earlier output, so a product invariant must contain their recombination. Exact arithmetic evaluation gives:

| row | input L | input W | output L | output W (fatal row: D right) |
|---:|---|---|---|---|
| 1 | 11 | 1 | 1 | 101 |
| 2 | 1 | 1 | 101 | 101 |
| 3 | 11 | 101 | 1 | 10101 |
| 4 | 101 | 10101 | 101100101 | 11 |
| 5 | 11 | 11 | 1 | 1011 |
| 6 | 11 | 1011 | 1 | 101011 |
| 7 | 11 | 101011 | 1 | 10101011 |
| 8 | 101 | 10101011 | 101100101 | 11011 |
| 9 | 11 | 11011 | 1 | 1011011 |
| 10 | 11 | 1011011 | 1 | 101011011 |
| 11 | 11 | 101011011 | 1 | 10101011011 |
| 12 | 101 | 10101011011 | 101100101 | 11011011 |
| 13 | 101 | 11011011 | 1011011011100101 | 1 |
| 14 | 1011011011100101 | 1 | 10011011100101 | 101 |
| 15 | 10011011100101 | 10101 | 10110011011100101 | 11 |
| 16 | 10110011011100101 | 1 | 11011100101 | 1110001 |
| 17 | 11011100101 | 1 | 111100101 | 101 |
| 18 | 111100101 | 1 | 10101 | 10001 |
| 19 | 11 | 10001 | 1 | 1010001 |
| 20 | 101 | 1010001 | 101100101 | 1001 |
| 21 | 101 | 1001 | 01100101 | 1001 | **fatal D**

The construction has a simple algebraic structure:
1. The seed left 11 forces W -> 10W, while left 101 (derived by row 2) forces W -> scan(W), where scan discards D tokens through the next reversal then prepends 1 to the remaining suffix. Alternate these operations to obtain W=11011011 (rows 3–12).
2. Combine L=101 with that W. The forced D1000 then three D110 tokens and D00 create left A C C F A E in run notation (A=1g1, C=2g1, F=3g2, E=terminal1; the explicit bit string is authoritative). Subsequent rows expose C F; even-run merge turns the top into 4g2 (row 17). Thus even the repaired B-entry condition cannot hold in any product invariant.
3. Row 18 uses even4 to insert singleton followed by gap3 into W. Prepend10 (row 19); scan reverses on 1010 and introduces gap2 (row 20). Row 21's forced D1000 leaves exact fatal 1001.

All steps use the literal-equivalent macros of Agent31 and exact composed sweep rules. Reproduce with node grouped-product-obstruction.cjs. The witness is only 21 returns with finite strings, no long simulation or grammar approximation. It establishes that successful proof must preserve a **relation** between left and right stacks, even after blank excursions and even with exact stack languages. Grouping the B3 repair additionally does not change this witness: no row uses B3g2.

Next promising abstraction: exact right run stack (finite run-length classes) and finite left prefix/regular suffix grammar, opposite direction to the failed exact-left/right-prefix attempts. In particular the counterexample relies on incorrectly reusing the initial terminal left 11 with arbitrary W. Tracking actual left terminal context prevents that particular spurious sequence.
