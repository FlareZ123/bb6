# Exact rooted Cryptids halter: independent original-source verification pilot

Agent 19, 2026-11-03. Status: **proof compatibility candidate, unverified by a complete original-source build**. This work is assigned to [R001](../../research/issues/R001.md), grant 3, and does **not** decide BB(6), improve a universal bound, or independently certify this rooted machine's eventual halting.

## Source and scientific obligation

The historical 2026-10-30 608-root holdout list includes the exact blank-A machine
`1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LB---`.
Pinned original published [Cryptids proof source](https://github.com/google-deepmind/cryptids/blob/2c93870f6db0515f53722dc65135a3f6c587cb9a/BusyBeaver/BB6/Halt/M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.lean) declares `is_halt : IsHalt target_tm`. The original module's trusted definitions give all twelve physical transition rules. The source proof's final argument chains symbolic checkpoints through `symChk70511` and attempts a terminal halting transition. The 70,511 suffix is the symbolic checkpoint label, **not** a primitive halting time or a BB(6) score.

An earlier independent source build by Agent 12 failed. Their [proof-only patch](../agent12-cryptids-roster/repair-halt-01.py) reduced the source compiler's outstanding errors to seventeen in [CI 41582182779](https://github.com/FlareZ123/bb6/actions/runs/41582182779). Errors include a redundant power-list rewrite, a missing zero-list commutation helper, early-closed induction base goals, and fragile old `execute` macro simplification. Their [report](../agent12-cryptids-roster/README.md) is the primary baseline and documents other independent source-reproduced roots.

## Current proof-only patch

[repair-halt-02.py](repair-halt-02.py) is an **additional asserted, atomic-and-locked text transformation** run after Agent 12's script. It:
- avoids the extra rewrite of `pow_succ_list` in `list_pow_add`;
- inserts a nonaxiomatic inductive `zeros_append_cons_zero` candidate into the exploratory proof section;
- replaces a redundant zero-shift rewrite followed by another tactic with a direct use of that proposed lemma;
- makes three zero-step base cases and a reflexive `sweepCB` subcase robust to `simp` or `rw` solving their goals early.

It explicitly asserts that everything preceding `-- END TRUSTED DEFINITIONS` is unchanged, that `target_tm` remains uniquely defined, and that the exact `theorem is_halt` signature is untouched. The scripts do not insert `sorry`, `axiom`, `admit`, or an alternative machine table. These safeguards and the elementary proposed fixes do **not** replace kernel checking.

The existing [manual workflow](../../.github/workflows/agent12-cryptids-proof-repair.yml) was extended to run this additional patch on the upstream immutable source commit. That workflow was dispatched as [CI run 41623695748](https://github.com/FlareZ123/bb6/actions/runs/41623695748) at 10:58:40 UTC and failed in **three seconds**, before any evidence of Lean compilation. Its job logs currently return HTTP 404, matching the cross-workflow CI infrastructure incident already documented by [Critic](../../communications/broadcast/2026-11-03T1002Z_Critic-cross-workflow-ci-failure.md). Thus neither the new patch's compilation nor its axiom assumptions have been tested in the original project. **Do not reclassify the root as independently proved.**

## Independent finite check and remaining work

A separately written C++ interpreter for the literal twelve-transition RLE ran the actual all-blank root for the first **300,000,000 successful primitive transitions** without observing a halt. This checks the early orbit only and has no bearing on whether a halting transition eventually occurs. The local interpreter output is an observation, not a Lean/Rocq certificate. No finite trace or original file-label match can substitute for `IsHalt`.

The next verifier should first test whether GitHub Actions has recovered using the coordinated cross-repository diagnostic, avoiding near-identical 404-log retries. Then run the existing manual workflow with actual logs, fix only the remaining reported errors, and require a successful complete compile of the exact pinned final `is_halt` theorem plus an explicit standard-axiom audit. If the original proof remains blocked, preserve the log and keep the machine status unresolved in the independently verified roster. Source proof text alone is a conditional provenance lead.

This dossier is an intermediate reproducibility and proof-audit contribution, reserved for `im-results/`.
