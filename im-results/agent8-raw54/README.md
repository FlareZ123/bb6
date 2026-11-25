# Raw54 E1=0LE, E0=1LB: five-hole child reduction

Canonical raw54: `1RB---_1RC---_0RD---_1LD0LE_------_------`.
The current child is `1RB---_1RC---_0RD---_1LD0LE_1LB0LE_------`.
First-hole enumeration gives 1,515 split, 25,133 cycle, 8,567 last-hole and 1,146 open nodes (25^5 raw completions); observed maximum weighted halt 451. **The full child audit has not passed original-source Lean.** No global roster cut follows.

Of 1,146 open nodes, 1,065 have FAR candidates (1,058 frozen-bank hits, seven additional hits), 49 have affine sweep proofs, eight have arbitrary-tail strong-induction proofs, eleven have sparse n-gram certificates, and two have the new shared four-bit counter proof. The last 11 candidate-unresolved one-hole tables are listed in [unresolved.txt](unresolved.txt). The 49 affine, eight strong-induction and eleven n-gram witnesses were previously compiled against original sources from raw117 artifact 14997867504, source revision 988705d0e0d7de1b736777b1b66b324115d75fdb. The two new recurrence proofs were checked locally on a copied model of the original zipper primitives; their original-source consumer is pending.

## Two-leaf counter invariant

[Raw54Pair.lean](Raw54Pair.lean) handles IDs 2 and 72 (zero-based in the 88 original bank misses), which differ only at C1:
- 2: `1RB0RF_1RC1RA_0RD0LB_1LD0LE_1LB0LE_1RA---`;
- 72: `1RB0RF_1RC1RA_0RD1RB_1LD0LE_1LB0LE_1RA---`.

Let k count scanned groups of four ones, and w be a finite Boolean list encoding four-cell blocks 0000 and 0011 (right tape padded by zeros). At A the left word, nearest-first excluding the scanned zero, is (1111)^k 1010111. The right word including the scanned zero encodes w. Both blank runs enter (0,[]) after 21 and 19 steps, respectively.

The exact total return system, with positive primitive costs, is:
- (k,1::w) -> (k+1,w), cost 6 for ID 2 and 4 for ID 72;
- (k,0::w) -> (0,0^k 1::w), cost 12+4k;
- (k,[]) -> (0,0^k 1), cost 12+4k.

Here 0^k denotes k zero block digits. The reset uses a six-step prefix, a left sweep E1 that converts each four-one block to four zeros, and a six-step suffix. The rules close over every finite list, including the implicit blank suffix. Iterating the total map gives unbounded live prefixes without F1 for every assignment of that sole hole. Local Lean 4.36.0-rc2 checked the recurrence and family_next with only propext and Quot.sound using copied original Z0, step0, run0, rep, sweepL and join0. The source module imports Raw54Return and exports never via the existing zipper-to-original-machine transport; that import has not yet been compiled in this incarnation. The generator incorporates both candidate proofs and retains all eleven other leaves.

## Reproduction

The columns of sweeps.txt are the zero-based ID in the original 88 bank misses, table, state, left/right zipper words (- empty, V denotes rep P n), P, jump j, entry t, and cost coefficients a,b. Each witness proves run0 table t blank = family 0 and run0 table (a*n+b) (family n) = family (n+j) for every n, then uses orbit k = family (j*k). Example ID 3: E, empty left, right (001)^n 0011, entry 7, epoch cost 20n+52, jump 2.

```sh
python im-results/agent13-coverage/unpack.py
python im-results/agent8-raw54/generate.py --sweeps-only
python tools/lean_compile_closure.py --workdir /tmp/a8-raw54-pair --jobs 4 im-results/agent8-raw54/Raw54Pair.lean
python im-results/agent8-raw54/generate.py
python tools/lean_compile_closure.py --workdir /tmp/a8-raw54-cut --jobs 4 im-results/agent8-raw54/Raw54Cut.lean
```

The full audit must be checked before using its residual roster. Raw54 has other children; closure of this child alone cannot close the raw54 parent. Raw55/56 are distinct canonical siblings; raw126–129 are excluded by state-introduction canonicality.
