# Raw58 LF1 leaf 1188: a two-block growth theorem

**Status:** parameterized return, growth and exact blank entry kernel-checked locally in Lean 4.36.0-rc2 against the exact copied repository zipper/sweep definitions. Original-source `never` and full LF1 child consumer audit remain pending. The concrete proof module is [Raw58LF11188.lean](agent4-raw58/Raw58LF11188.lean), assigned to LF1 in `more.json`.

## Exact recurrence

The zero-indexed LF1 open leaf 1188 is

`1RB1LF_1RC0LB_0RD1RF_1LD1RE_---0RA_1LB0RF`

(E0 is its sole undefined transition). Let B denote state 1 of the head-relative zipper; its left list includes the scanned cell and an empty left list means an all-zero left half. Define

- H = `01111111100`
- P = `11110000`
- M = `1111001100000011110001111111110000000000000000`
- W = `11111100`
- T = `1111110011111100111111000000111100000000111111`.

For **every natural n and every right-tail list R**,
```
run0 table (7142+784*n) B([], H ++ P^n ++ M ++ R)
    = some B([], H ++ P^(n+6) ++ M ++ W ++ R).
```

The authentic blank enters B([], H P^31 M T) after exactly 88544 steps. Thus the family B([], H P^(31+6k) M W^k T) has a strictly positive growth cost 7142+784(31+6k), for all k. `never_of_growth` yields nonhalting for every compatible completion. This resolves the last previously unassigned LF1 leaf at the symbolic-proof level, conditional on original-source acceptance.

## Proof construction

The orbit initially has changing run-length patterns. At frontier return number 74 (zero-indexed), the repeating 14-phase macro begins. Comparing successive 14-phase samples revealed two independent growth blocks: six copies of the 8-cell P on the left and one copy of the 8-cell W on the right. The full symbolic return is **not** inferred from extrapolation: the Lean module contains 29 literal transition segments (7142 total primitive moves) and 28 arbitrary-tail block transfers (14 rightward 32-step and 14 leftward 24-step transfers per copy, 784*n total). Every elementary transfer is checked by rfl for arbitrary untouched lists and lifted using SweepPumping.sweepL/sweepR. The final rotated block 00011110 is converted to P using a list rotation identity. The entry is proved through 23 exact primitive-step chunks (22 of length 4000 and a final 544).

Local Lean checks passed all 57 segment lemmas, composed return1188 and growth, and every entry chunk plus composed entry. return1188/growth/entry have only propext and Quot.sound; no sorryAx or native_decide. The exact remote proof blob SHA-1 7069305a7bdbc62459c667a2b02857299bcf13b2 matches the locally constructed source (module header imports original Raw58Live, and the never bridge is appended to the checked recurrence/entry bodies). The local dependency closure was copied because direct GitHub clone DNS is unavailable in this container; the final original-source module and consumer remain to be audited.

The module was committed at d0e0ad95444e0870dda88c4090833b4e673dfa80, assignment at ab58c8292bc9cdea23d09ae70a6ce17d4bf93d83. Reuse the existing LF1 audit/shard workflow; do not launch a separate workflow or reinstate the large RLE search.

## Scope

Every previously unassigned LF1 open leaf now has an explicit symbolic or exact late-query assignment. This does not establish full child closure: existing other leaves and original-source equality/never checks, generated Kid shards, and parent composition must pass. No unconditional global Cover or BB(6) maximality claim follows yet.
