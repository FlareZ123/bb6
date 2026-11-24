# Replaying constructive reachability proofs at exact indices

## New method (local fixture validated; actual upstream adapters pending)

The constructive proof of a finite execution contains its primitive-step witness even when its statement existentially hides the index. The Lean metaprogram WitnessExtract.lean transforms the proof rather than re-proving the tape evolution from scratch. Its output is an ordinary kernel-checked theorem of ReachesIn with the original machine, binders and endpoints. It does not add axioms or assume an unverified numerical count. It fails if it cannot reconstruct a proof.

The fixed-index extractor reads imported theorem bodies (including private declarations when imported by an ordinary non-module file), preserves primitive transition equalities, replaces existential head/tail/transitivity with exact-index combinators, and transports the exact relation through original equality rewrites. Its congruence transformation handles both whole and partially applied reachability relations. The Nat-rec replay replaces the induction motive with the specified indexed relation, substitutes the new indexed induction hypothesis, and proves the resulting cost equalities using omega. The composed extractor substitutes previously established exact companions.

Local Lean 4.36.0-rc2 regression against a synthetic BusyBeaver interface and toy machine passed fixed counts 3, 5, 8, imported private declarations, simp/rw transports, the 3*k induction, and composition at 3*k+3*k. A deliberately incorrect requested count was rejected. This fixture is not an upstream TM verification.

## Original-source trial

F424Extract.lean and F412Extract.lean attempt to extract 20 fixed-cost and 3 variable-cost theorems each from the original unmodified halt proofs. They start with the two previously blocked atomic declarations step_CB_run1 and step_CB_run_ge3. The proposed variable-length costs come from the original primitive execute scripts and sweep composition; the kernel must check them. F424 and F412 are NOT classified below the champion by this work.

Use the existing manual shared-cryptids-source-audit.yml workflow:
- upstream_sha: 3647718b5df22e1a61462dec0376bd204526285a
- lean_toolchain: leanprover/lean4:v4.36.0-rc2
- dependency_version: v4.36.0-rc2
- original_module: BusyBeaver.BB6.Halt.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH
- dependency_path: im-results/agent49-witness-extract/WitnessExtract.lean
- bridge_path: im-results/agent49-witness-extract/F424Extract.lean
- expose_solution_declarations: false (preserve the original module)

F412 uses BusyBeaver.BB6.Halt.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA and F412Extract.lean. Run the original-source trial before using the generated theorems in a frontier classification. No dispatch capability was available through the current connector.

## Shared F412 counted-proof dependency repair

Agent 26's [run 45408321030](https://github.com/FlareZ123/bb6/actions/runs/45408321030) fails at the very first bridge import: `cannot import non-module SourceCostModel from module`. Its original F412 source build succeeded. The fix changes only the header and export scope of Agent 11's `SourceCostModel.lean`: `module`, `public import`, `@[expose] public section`, and the matching `end`. Definitions, costs, and existing examples are unchanged. A local Lean 4.36.0-rc2 minimal module regression confirms that an exposed public definition remains reducible to both module and legacy consumers. The actual upstream dependency closure still requires the targeted source audit. The earlier 20 fixed F412 atoms were already checked individually by Agent 26; no duplicate fixed-atom audit is needed.

The next mathematical gate is `F412CountedPure.lean` (full exact primitive and pure dispatcher semantics). The source checkout is unavailable locally due to DNS resolution failure, but the supplied Lean compiler is usable. SourceAffineBlocks will need a compatible module export when the counted macro layer is reached; do not broaden the current audit before Pure compiles.

## Limitations

Only supported proof shapes are replayed. Arbitrary elimination, dependent recursors, opaque or unavailable source bodies may require additional implementation. The complete shared symbolic-run and bounded-cost graft is still required. This is an intermediate method/tool, not a completed BB(6) proof.
