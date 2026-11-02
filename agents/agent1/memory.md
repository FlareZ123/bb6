# Agent 1 continuity

Claim: run `a6243f30-c4e8-46d5-8e6e-51b2a30d9ac3`, original lease `2026-11-02T00:44:25Z`. Never refresh the lease. Follow the 70-minute checkpoint rule and release only when measured age >=70 minutes; at 70+ complete cleanup then delete lease as the final repository mutation.

## Scope and current findings (2026-11-02)

Primary goal remains an exact, rigorously proved BB(6). There is no claimed solution, bound improvement, or newly decided machine.

Research and source files already committed:
* `im-results/agent1-p1-map/README.md`: source, independent small-step/macro verification, evidence limits, dynamical-system open problem.
* `im-results/agent1-p1-map/verify_p1.py`: reproducible direct machine simulation, verified 100 accelerated transitions (112,669 raw steps); 100,000 macro steps from P1(2,1) with no halt.
* `im-results/agent1-p1-map/GParity.lean`: self-contained Lean 4.36.0-rc2 with four theorems and `#print axioms`; no `sorry`. Formalizes parity of nested drain G, exact halting gate, and pre-halt predecessor constraint. This is an arithmetic restatement of Google DeepMind's *already certified* reduction of `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`, not independent TM bridge.
* `resources/BB6_holdouts_663_2026-10-16.txt`: 663 entries, all distinct and RLE-validated, mirrored from Dojo-1/cryptid-verifier/analysis/appendix-c-leads/holdouts-663.txt, originating https://wiki.bbchallenge.org/w/images/6/69/BB6_holdouts_663.txt , listed 2026-10-16. Source mirrored GitHub blob sha `e514d067c1ae1714cfafd1da1e94d1a039150b36`; source SHA256 in Dojo-1's census is `cfb2540f8101f2f2f20a14f9bc848252e34e45de2920fdd6b257096093844ee9`. Must refresh if a newer list becomes public.

Existing published formal work: https://github.com/google-deepmind/cryptids/tree/main/BusyBeaver/BB6 . Open questions include analyzing reachable `P1(a,4)` with even a. The local proposed naive invariant c odd or zero fails at accelerated transition 45. One million accelerated steps from P1(2,1) did not halt and reached (1376716, 621355). Infinite nonhalting does *not* follow.

Recent new computational structural screen, not yet preserved as code: Enumerating all 720 state-label permutations x tape reflection, ignoring distinguished starting state A, grouped 663 holdouts into 435 exact transition-table families, 145 nonsingletons and 373 members in those families (largest size 5). Fixing initial state A gave 663 distinct equivalence classes. The 435 count does not collapse 663 independent blank-tape halting questions: different starts on the same table may have different outcomes. Comparing first 300 raw configurations for all 373 starts found no equal up-to-translation cross-start states; screening all 663 for 10,000 raw steps found no halts and no exact translated tape cycles (hash candidates verified by full tape). These short negative screens are limited and likely anticipated by existing research, not academic results. Save reproducible code and input hashes if working further.

## Research priorities

1. Prefer uncovering a general symbolic invariant or complete finite certificate on a presently listed unresolved representative; use public DeepMind modules to avoid duplicating completed reductions.
2. Work from rigorous, exact semantics; prove any new macro rules for *all* input parameters (e.g. in Lean). A mere long trajectory provides no nonhalting proof.
3. All experimental or administrative discoveries in `im-results/`. Only promote genuinely publishable mathematics to `results/`.
4. Research can use local Lean at `/tmp/lean/lean-4.36.0-rc2-linux/bin/lean` (archive in /mnt/data). GitHub connector writes commit+push. Repo README forbids per-commit CI.
5. The repository was near empty at start, agent1 memory was initially empty; other identities may now operate concurrently. Check broadcasts and revalidate branch heads when modifying shared files.

Progress should be reported in commentary while working.
