# Raw54, E1=0LE, E0=1LB — sweep discovery checkpoint

Canonical residual 54: `1RB---_1RC---_0RD---_1LD0LE_------_------`.
The E1=0LE, E0=1LB child is `1RB---_1RC---_0RD---_1LD0LE_1LB0LE_------`.
First-hole enumeration of this five-hole child (25^5 = 9,765,625 raw completions) yielded 1,515 split, 25,133 cycle, 8,567 last-hole and 1,146 open nodes; observed maximum weighted halt 451. The tree and its bound remain candidate data pending the original-source Lean audit.

The ordered bank is a frozen union of six existing FAR banks (426 distinct entries). It hit 1,058 of the 1,146 open nodes. Seven more hit the two 5-state DFAs specified in generate.py. The remaining 81 are all one-hole partial tables. Forty-nine exact affine sweep families were found by symbolic opaque-block execution, then generated using the Agent8 raw112 multisweep approach. All 49 generated proof modules passed Lean 4.36.0-rc2 against a local standalone model with the original Z0, step0, run0, rep, sweepL/R and moveCut definitions/lemmas, and a separately proved zipper-completion nonhalting theorem (axioms propext, Quot.sound only). This was a local mathematical preflight, NOT original repository-source acceptance. The remaining 32 tables are listed explicitly. No claim of closure of the parent or change of global residual count.

The columns of sweeps.txt are the zero-based ID in the original 88 bank misses, table, state, left and right zipper words (- empty, V denotes rep P n), P, jump j, entry t, and cost coefficients a,b. Each witness proves run0 table t blank = family 0 and run0 table (a*n+b) (family n) = family (n+j) for every n, then uses orbit k = family (j*k). The source generator imports the actual SweepPumping module. Example ID 3: E, empty left, right (001)^n 0011, 7-step entry, epoch cost 20n+52, jump 2.

Reproduce:
```sh
python im-results/agent13-coverage/unpack.py
python im-results/agent8-raw54/generate.py --sweeps-only
python tools/lean_compile_closure.py --workdir /tmp/a8-raw54-sweeps --jobs 4 im-results/agent8-raw54/Raw54Sweep*.lean
python im-results/agent8-raw54/generate.py
python tools/lean_compile_closure.py --workdir /tmp/a8-raw54-cut --jobs 4 im-results/agent8-raw54/Raw54Cut.lean
```
The partial audit generator is not yet replayed against the original dependency closure. Preserve every unresolved leaf, and do not graft the child into a global proof without source acceptance. The 32 unresolved leaves are available for new deciders. Raw54 is still not covered by this child alone. Raw55/56 are other canonical siblings; raw126–129 are excluded by state-introduction canonicality and should not be researched as separate parents.

## Second checkpoint (15:39Z)
All 49 affine sweeps rebuilt and checked using the original sources from accepted raw117 artifact 14997867504 (source revision 988705d0e0d7de1b736777b1b66b324115d75fdb). Eight new arbitrary-right-tail strong induction certificates (IDs 38,39,40,42,56,61,67,69) also checked locally with axioms propext, Quot.sound. Eleven small sparse n-gram certificates (30,43,45,46,47,54,55,58,60,78,79) checked with only propext, Classical.choice, Quot.sound. The n-gram certificates regenerate from the same ordered miss roster and exact existing emitter. Remaining 13 are in unresolved.txt. The first five-hole child audit is still awaiting full kernel verification; no claim of global coverage or exact BB(6). Corrected reversed FAR bank command arguments.
