# Raw45 C1=1RE: exact local maximum 473

**Full original-source kernel-checked local theorem, 2026-11-28.** Parent:
`1RB1LB_1RC0LA_0RD1RE_1LD1RB_------_------` (four holes; 390,625 physical completions). All halting completions halt in at most 473 attempts, including the halt. The maximum is attained by `1RB1LB_1RC0LA_0RD1RE_1LD1RB_0RF0RE_---0RD`, with F0 assigned halt. This is a strict subcylinder of Raw45.

The exact audit has 93 split nodes, 1,489 translated-cycle leaves, 139 affine sweep witnesses, 20 two-sided n-gram witnesses, one independent quadratic recurrence and 491 last-hole queries. Each internal split includes all 24 ordinary actions and the explicit halt action. Each last-hole query includes the halt alternative and 24 total nonhalting-transition tables. Every certificate is checked against the actual refined table. All 12 slots must match when attaching a semantic proof or subcover.

The hard growth example has D-return law D(n) -> D(2n+4) in 7n²+41n+59, from D(0) after three moves. The second late residual has an alternating-block affine pump, captured by the certificate dataset.

The exported `BB6.Agent24Raw45.Raw45ReParent.cover : Cover (DecidedBelow 473) parent` and `BB6.Agent24Raw45.ReWitness.exact_parent_max` were accepted by Lean 4.36.0-rc2 (b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a) with only [propext, Classical.choice, Quot.sound]. All 24 child modules and final assembly exited zero. Original repository dependency blobs matched. No native-decide oracle or admitted assertion was used.

## Reproduction

Run `bash reproduce.sh` from the certificate directory with Lean 4.36.0-rc2 (JOBS=1 on low-memory machines). This checks dependency Git hashes and materializes 25 generated modules (246,984 source bytes) from the compressed certificate dataset, checks their combined SHA-256, then compiles the exact import closure. Lean checks every query, branch, cycle, pump, n-gram and attachment. The shell wrapper itself has not been executed in a repository checkout; the corresponding exact sources and emitted modules were compiled locally.

For integration, materialize the generated modules with `python3 emit.py certificates.json.xz <build-directory>`. This supplies an ordinary blank-step bound; the standard weighted-first-one margin gives 478 once the weighted bridge is compiled. No Canonical38 roster decrement is justified yet.


## Earlier quadratic recurrence dossier

# Raw45 C1=1RE four-hole subtree

Parent: `1RB1LB_1RC0LA_0RD1RE_1LD1RB_------_------`. It first reads E0 after 12 ordinary steps. This is a sub-obligation of the still-open Raw45 root; the current global Canonical38 count is unchanged.

## Certified nested sweep

The residual `1RB1LB_1RC0LA_0RD1RE_1LD1RB_1LA1RF_---0RB` never halts for **any of its 25 physical F0 completions**. [Raw45ReQuadratic.lean](Raw45ReQuadratic.lean) proves this in the original raw semantics by the existing SweepPumping zipper bridge. It is not an affine automatic-pump certificate: the D-return time is quadratic.

Write the head-inclusive left word first, nearest cell first. Let
- D(n) = (D, 00 1^(2n+2), empty).
- E(a,b) = (E, 1111, (1010)^a 11 (10)^b 1).

From blank, three steps reach D(0). A 2-step B/A packet transfers 11 to 10; a 10-step E/F/B/C/A packet transfers 1010 to 1111. The exact nested sweep is

- D(n) -> E(0,n) in 2n+21 steps.
- E(a,b+1) -> E(a+1,b) in 14a+22 steps, by consuming the first right marker and resetting the growing prefix.
- E(n,0) -> D(2n+4) in 24n+38 steps.

Summing the middle costs gives 7n²+15n; hence D(n) -> D(2n+4) in 7n²+41n+59 steps. All packet claims are literal computations with arbitrary untouched tails where applicable; the middle iteration is induction, not sampled extrapolation. Since the return costs are positive, the original raw machine has arbitrarily long live prefixes without reading F0.

**Local acceptance:** Lean 4.36.0-rc2 (b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a). The exact transitive repository sources were copied into the local shell, verified using Git blob SHA-1, and compiled in order. Both `BB6.Agent24Raw45.ReQuadratic.growth` and `BB6.Agent24Raw45.ReQuadratic.never` depend only on `propext, Quot.sound`; no sorry or native oracle.

| Module | Repository path | Git blob |
|---|---|---|
| Frontier | im-results/agent8-coverage-contract/Frontier.lean | 115438c4f244b5416a91be4dd7a3f12103d5448d |
| Symmetry | im-results/agent8-coverage-contract/Symmetry.lean | 84f62dcea34e7f2a97d07016cc2d9065d4ddd7ce |
| RootShift | im-results/agent8-coverage-contract/RootShift.lean | 80b56fb040f7db81277fcf52cd43e6127fe365ba |
| SparseZipper | im-results/agent50-weighted-tnf-pilot/SparseZipper.lean | 8081dc82ca1e892ab2f6c698d94b6dc24129f6e6 |
| SweepPumping | im-results/agent31-three-hole-tnf/SweepPumping.lean | e518c288ecdf5c96890ad64b5971f5c2f18a2106 |
| Raw45ReQuadratic | this directory | 3fa514d27feb8ee306ec24787a20119575fa2b67 |

Reproduce by compiling each source with `LEAN_PATH=.` and `lean -o Module.olean Module.lean` in a common temporary directory, last the new module. The direct original-machine theorem is `never`.

## Parent discovery and remaining work

[scan.py](scan.py) reproduces a first-query tree with a 250-step cap, exact one-sided translated cycles (last 32 same-state configurations) and the existing Agent48 automatic pump search. It emits 91 ordinary split nodes below the root, 1,487 cycles, 468 last-hole queries, 136 pump candidates and 26 open leaves; largest recorded query time 231. The root is an additional split. Each ordinary split has all 24 ordinary choices and its explicit halt alternative. Counts are exploratory, not a checked parent Cover.

The existing Agent1 ngram.cpp generator at widths <=9 supplies 20 certificates among the 26 open leaves. The certified quadratic theorem handles open leaf index 1; the other five reach a previously unassigned transition at ordinary times 323, 276, 322, 322 and 359 respectively (open indices 12,16,18,20,25). Continue from these actual queries, preserve proof bank and produce one complete source-checked weighted parent audit rather than a collection of isolated candidates. Reuse existing ZipThreeHoleAudit, Agent46AutoPump and NGramCertificate checkers.
