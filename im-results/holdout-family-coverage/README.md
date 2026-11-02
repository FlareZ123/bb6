# Auditable BB(6) rooted-transition-table portfolio ledger

Intermediate research infrastructure, Agent 3, 2026-11-02.

[2026-10-16-rooted-ledger.csv](./2026-10-16-rooted-ledger.csv) contains **663 rows** for the **pinned 2026-10-16 snapshot** in `resources/BB6_holdouts_663_2026-10-16.txt`; this is not necessarily the current set of undecided machines. There are **435 canonical unrooted transition-table families**, including **145 multi-root families**. The groups were recomputed by exhaustively considering all 720 six-state permutations and optional left/right reflection. The canonicalization must keep the blank symbol fixed; it permits no exchange of symbols 0 and 1.

The source is reproducible with `tools/holdout_family_ledger.cjs` (Node.js CommonJS, no file writes), which reuses `tools/holdout_families.cjs`. A separate manual GitHub Actions job compares fresh generator output byte-for-byte with the committed CSV. Its source, rules, and cardinality checks are auditable.

## Column meanings

- `rooted_rle`: the original six-state RLE in the pinned snapshot; its designated blank initial state is A.
- `family_id`: stable within this exact snapshot, assigned by sorting the canonical unrooted RLE; do not interpret as a numeric halting classification.
- `canonical_unrooted_table`: lexicographically minimal transition table over all state permutations and reflection.
- `canonical_start_for_root`: the original root A expressed as a state in its canonical table. This field is indispensable: machines with equal canonical tables can have different blank-start outcomes.
- `mirror_original_to_canonical`: whether the chosen witness reflects directions and physical tape coordinates.
- `canonical_state_order_original_letters`: six original-state letters appearing in canonical A,B,C,D,E,F positions, respectively.
- `family_member_count`: number of roots of that table **appearing in the snapshot**, not the orbit size under the entire symmetry group.
- `local_proof_status`, `local_source_path`, `local_ci_run_id`: conservative, source-linked entries for eight manually curated roots. The other 655 rows say *not curated*, which does **not** mean unproved, unsolved, or independently verified.
- `global_rooted_halting_status`: one reviewed F287 root is marked **nonhalting from upstream proof**; all other entries retain `not established by this ledger`. No classification is inferred from a table-family match.
- `external_status`: pinned Cryptids source provenance for the reviewed F287 root; `not checked` for the other 662 roots. The snapshot may be stale relative to external developments.

## External machine-level nonhalting evidence: one dated root

On **2026-11-02**, Agent 6 checked the original pinned [Cryptids source at commit `c86f15861709b76042998c5211c7b2f83991621b`](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LBHHH.lean). It defines exactly the rooted RLE `1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---`, and states the complete *blank-tape* theorem `is_not_halt : IsNotHalt target` and its bridge `not_halts : ¬ ConjectureMachines.Halts machine`. [The upstream A6 proof guide](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/artifacts/a6/README.md) documents its certified entry and positive-time affine return family and supplies an axiom-audit module. This is upstream prior research. The pinned upstream [BusyBeaver CI run 41440419564](https://github.com/google-deepmind/cryptids/actions/runs/41440419564) **succeeded**, including the `BusyBeaver` Lean build and the independent-format comparator step. Agent 6 inspected the pinned source and upstream CI but did **not** independently compile the entire upstream dependency chain in this repository.

This machine is row **F287** in the pinned October 16 catalogue and is now explicitly tagged in the CSV as **externally proven nonhalting**. The snapshot of 663 rooted strings is a *historic inventory*, therefore it must not be treated as 663 presently unresolved machines. One proven member does not establish the current official undecided-machine count, which would need separately dated external source verification. Other rows with `external_status = not checked` remain **unreviewed**, not classified open.

## Concrete high-multiplicity D-family evidence

The four-root family **F341** is independently source-certified in `im-results/agent3-portfolio-raw-conjugacy/DTableWitness.lean`, [manual CI 41457732702](https://github.com/FlareZ123/bb6/actions/runs/41457732702). Its canonical starts are **D, F, B, C** in the corresponding catalogue rows. When transported instead into D0's own original transition table, those are **A, F, C, B**. These are mathematically equivalent descriptions under different common-table coordinatizations. All four remain genuine, separate blank-origin halting questions.

Other annotated source bridges and their CI IDs are in the CSV itself. Their status summaries are intentionally restricted to the particular rooted machine and do not propagate to other roots merely from table isomorphism.

## Remaining research task

A solver can reuse machine-specific raw transition lemmas across family members via the general Lean theorem `relabel_reflect_haltsAt_iff`, but must independently derive or decide each original A-start orbit in its mapped canonical start. Add verified outcome evidence to a root only after a source-checked blank-origin proof. Maintain an independently dated review of external holdout decisions before interpreting this historic snapshot as a current BB(6) frontier.

The ledger belongs in `im-results/` and never purports to improve the BB(6) lower or upper bound.
