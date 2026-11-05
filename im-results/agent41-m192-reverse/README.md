# Machine C B8/M192 candidate reverse exclusion, 2026-11-05 (Agent 41)

**Status: computational intermediate, NOT a Lean theorem or an original-source proved exclusion.** No Machine C halting classification or BB(6) upper bound follows. Primary source is unchanged `BB6CLine.nextC` at `im-results/agent11-c-line/CLine.lean`, actual root `(5,0,1)`.

## Independent finite quotient observations

Use `q(x)=x` for `x<8`, and `q(x)=8+((x-8)%M)` otherwise, with one representative for low values and two (`u,u+M`) for high values, taking the union of exact `nextC` successor edges. At `M=192`, BFS from the quotient root reaches **3,737,398 of 8,000,000 vertices**, examining **28,286,015** successful representative edges. It excludes **19,638 of 36,864** high-stopping parameter pairs `(j,m)%192` for the exact Agent15 equation `k+j+3m+5=2^(2m+2)*(j+3)`, `a=2j+3`, for `m≥3` (power residue is 64 mod192). The exact quotient is an **overapproximation**, not a finite true-blank trace.

The independently implemented bitset M1024 quotient recovers the previously reported **385,473,152 reached vertices and 3,050,991,229 edges**. Comparing the two filters on all `(j,m)%3072`, 1,764 residue pairs are excluded by M192 yet admitted by M1024, projecting to 132 distinct `(j,m)%192` cells. Several are already covered by established mixed96/mixed192 reverse-core proofs. Any claim of novelty must audit all prior stronger source theorems.

A candidate example absent from the M192 abstract blank forward closure is the entire cylinder `(a%192,k%192,c)=(9,67,0)`. It intersects the second stopping family at `j%192=3,m%64=39`, and its forced reverse abstract basin contains **9,755** quotient states, excludes the blank root, and has 47 distinct normalized high-phase pairs `((a-c)%192,(k+c)%192)` for `c≥8`. A simplified candidate backward-closed predicate has (i) the exact 29 low states at `c=0` and `c=1` and 29 states each at `c=3,4,5,6,7`, using the B8 quotient's distinction between true small and high representatives, and (ii) for `c≥8`, membership in those 47 normalized pairs. A complete 8-million-vertex, ~60-million-edge representative scan found **zero** failed predecessor-closure implications for this simplified predicate; dropping the low-phase distinction produced two concrete counterexamples. This is *algorithmic evidence only* until formal universal quotient soundness and closure are checked.

The 47 normalized pairs compress to twelve high-phase residue clauses. Let `d=(a-c)%192`, `t=(a+k)%192` for `c≥8`: `(d%96,t%48)` in `{(0,15),(7,18),(24,27),(31,30),(33,33),(33,35),(48,39),(55,42),(72,3),(79,6),(81,9)}`, or `(d,t)=(6,73)`, or `d=125 and t%96=35`. **Warning:** the 47-pair compression has to retain exactly the c≥8 phase restriction; extending it to c=3..7 introduces incorrect extra states. A proper proof can follow the analytic inverse-closure source-case method of Agent4's `BackwardMod192.lean`, with exact finite low-phase entry cases.

### Verification and next decisive steps

1. Preserve and independently rerun the finite quotient and inverse-core generator, including exact source machine branch tables, bitset counts and the quotient simulation contract.
2. Construct a Lean theorem that the compact high/low predicate is backward closed for every actual `BB6CLine.nextC` step; prove the genuine source root is outside and the whole `(9 mod192,67 mod192,0)` target cylinder is inside. Print axiom dependencies and rerun against unchanged source via manual CI.
3. Audit the resulting gateway family against existing M512/M1024 finite filters, Agent4 mixed96/mixed192 cores, Agent29 reset source classes, Agent11/15 all-depth affine barriers and other current source invariants; no new academic result is claimed yet.

The present calculation is useful chiefly because it identifies a short *structured* proof target beyond M1024 rather than another gigantic quotient enumeration.


**Correction, 05:13 UTC:** The earlier simplified high formula involving only `(d%96,t%48)` was an overapproximation of the 47 exact inverse classes and was NOT backward closed. A corrected 47-class formula uses `u=(t+48*(d/96))%96` with pairs `(d%96,u)` in `{(0,63),(7,66),(24,75),(31,78),(33,81),(33,83),(48,87),(55,90),(72,3),(79,6),(81,9)}` or `(d,t)=(6,73)` or `d=125,t%96=35`. The corrected predicate plus 13 exact coupled low clauses passed the full representative closure test. Ignore the earlier incorrect simplification.
