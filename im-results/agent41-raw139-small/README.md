# Raw139 D1=0LE / E1=1LF finite subcylinder audit

The exact parent table is `1RB---_1RC---_1LD---_---0LE_---1LF_------` (first-use prefix B0=1RC, C0=1LD, D1=0LE, E1=1LF). This is the seven-hole child of raw139, not an entire canonical root.

A deterministic finite simulation and FAR saturation construct a **candidate** partial coverage contract at bound 512. The generated Lean module reuses the repository's ThreeHoleAudit and first-hole weighted halt theorem. **Source build not yet accepted**; no new kernel-certified coverage count is claimed at this checkpoint.

The four early continuation edges F0=1LD, D0=1LA, B1=0RC, C1=0RB retain all alternative children, including 75 open branches and 17 side-cycle witnesses. E0 is the first hole at step 25. All E0 instructions are handled; each next queried hole is expanded over all 24 ordinary moves, and the corresponding halt alternatives are charged at their actual query times. Within the three-hole E0 cylinder, 161 side-cycle witnesses, 116 last-hole witnesses, 15 explicit FAR witnesses, and 8 unresolved one-hole cylinders occur. The largest last-hole query is 321; the weighted bound 512 is conservative. The nine unresolved one-hole tables include the previously identified upstream Cryptids machine (F1 never queried); it is deliberately left open in this independent finite module.

The entire candidate residual list has 83 leaves, with raw completion mass 4793672075 out of 6103515625. The E0 cylinder alone has 15,625 raw completions and 225 open completions if the finite validators accept; the nine one-hole cylinders are not proven halting or nonhalting by the search. The local C++ simulation of all nine reached 10 million steps without a halt; no conclusion follows from that cutoff.

Files:
- Raw139SmallAudit.lean: candidate source-connected partial-audit theorem and generated witness tree.
- generate.mjs: deterministic finite-witness regeneration (Node.js); no dependencies.
- witness-data.json: generated data, exact open tables and addresses, counts.
 
Compile the new module using the original ThreeHoleAudit/FourHoleRootFrontier closure and Lean 4.36.0-rc2. Audit `parent_contract` and the finite checker theorems for axioms. Do not import the heavyweight champion score into this finite certificate; lift its bound symbolically only after acceptance. A prior draft's raw139 literal had incorrect B1/C0 direction bits, fixed separately in commit bce2489569613476458dd30da6611e94ea2a7cea.
