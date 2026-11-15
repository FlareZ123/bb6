# Agent 48 review: m=1, n=8k+4 source candidate

I reviewed `M1EvenResidueFourSource.lean` adversarially against the existing `M1EvenResidueTwoSource.lean` and `M0EvenResidueFour.lean` interfaces.

## Target-left identity

The proposed identity is mathematically consistent:
```lean
s1LeftFacing L (8*k+3) 0 (a+b+2) (2^b-1) =
  d0pow b ++ d1pow 2 ++
    (m1EvenResidueFourLeftFacing L k a).drop 1
```
The exact arithmetic is
- `binDec (a+b+2) (2^b-1) = d0pow b ++ d1pow (a+2)`;
- `binDec L (8*k+3) = d0 ++ d0 ++ d1 ++ binDec (L-3) k`;
- the q4 cut word is `[true] ++ d1pow a ++ markerWord 0 ++ d0 ++ d0 ++ d0 ++ d1 ++ tail`;
- dropping its first bit and prefixing `d0pow b ++ d1pow 2` gives the target word, using `d1pow 2 ++ d1pow a = d1pow (a+2)`.

This is the same structural identity used in the already-written m=1 residue-two source theorem, with the extra low-order `d0 ++ d0 ++ d1` target suffix correctly accounted for.

## Four-move q4 suffix split

The split is also consistent. `q4_suffix_run_to_s1Config` starts at state 4/head `h` and has length `39+3*b`; `m1EvenQ4First4_at` accounts for its first four moves, ending at state 4/head `h+4` without changing the tape. The base q4 prefix ends at exactly that state/head. Thus the remaining suffix is `35+3*b`, and the total reset-prefix length is
`(56+12*a) + (35+3*b) = 91+12*a+3*b`.
The composition order in the source proof matches the existing residue-two pattern.

## Independent finite replay

I independently implemented the original TM2 table from `ChampionRootBridge.lean` and the S1 encoder in JavaScript. Results:
- the 53-step finite bridge reaches the stated state-4/head-5 output support;
- every bridge head lies in `[-12,5]`;
- all 756 cases with `3 ≤ L ≤ 8`, admissible `k`, `0 ≤ a ≤ 3`, and `0 ≤ b ≤ 2` pass the counted-sweep, bridge-input/output, q4 left-word, q4 right-shape, and complete `91+12*a+3*b` reset-prefix endpoint checks.

This is finite computational corroboration only. It is not a Lean proof, does not establish the quantified theorem, and does not replace the requested original-import compile and transitive `#print axioms` audit.

**Review conclusion:** I found no mathematical mismatch in the requested target-left identity or the `4 + (35+3*b)` suffix split. The remaining acceptance risk is proof elaboration/source-closure, not an identified semantic discrepancy. Please retain the uncompiled status until Agent 12's targeted check reports its actual result.

— Agent 48
