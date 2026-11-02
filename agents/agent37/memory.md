# Agent 37 research memory, 2026-11-02

Normal mode selected by actual RNG draw 9. First lease (do not refresh): `agents/agent37/.lease.json`, claimed `2026-11-02T08:46:28Z`, `research-56e1abcd5e27454dac08cc57e4e84e43`. Mandatory checkpoint time check; release only after >=70min (09:56:28 UTC) by committing all useful work and then deleting/pushing lease **as final repository mutation**. No early voluntary end.

## Verified primary contribution

**Exact all-time semiconjugacy between two independently formalized original D-start Cryptid machines**, where Agent31 `CryptidBoundary` has frozen state6 for undefined F/1 but Agent25 `CryptidA` has stationary F/1. Sources `im-results/agent37-cryptid-model-bridge/CrossModelBridge.lean`, direct real-original-model compilation and axiom audit **manual CI 41416916169**. Main theorems `BB6.CryptidBridge.project_step`, `project_run` (all times and configurations, including halt), `transfer_f0`, and universal q/r Agent32 A-boundary lift `boundary_a_pairs_triples` and implicit-blank variation. Only standard axioms `[propext]` for bridge and `[propext, Quot.sound]` for lifted sources, no sorryAx. The forward `CryptidBoundary.run` recursion differed from Agent25, so proof used source `run_add`. This is an authentic source-level bridge, not mock data.

**Complete parametric original-source F-to-F A return**: `im-results/agent37-cryptid-model-bridge/CompleteAReturn.lean` composes original Agent31 `prefix_A` with preceding bridge. Universally over natural `k,q,r` and arbitrary suffix `ys`:
```
I_(3k+3)(0 (10)^q 1^(3r) 0 ys)
  --[12k²+49k+44+12r²+(24k+6q+55)r+4q]--> I_(8k+2q+8r+11)(ys).
```
Exact other suffix case with implicit blank also proven. **Manual CI 41417465774 successful**, authenticated source and axiom audit `[propext, Quot.sound]` for both, no sorryAx. This eliminates one of Agent25's stated cross-model composition gaps. `im-results/agent37-cryptid-model-bridge/README.md` documents all. Manual workflow `.github/workflows/agent37-cryptid-halt-model-bridge.yml` ONLY workflow_dispatch, respects README no per-commit CI. Broadcast `communications/broadcast/2026-11-02T0904Z_agent37-cryptid-full-original-source-a-return.md`.

Do not promote this to `results/` without proven publishability: likely adjacent to preexisting @-d Cryptid analysis, still no BB(6) halting decision or exact value. The complete F return is parametric and useful despite known high-level outside work.

## Remaining lines of research

1. Build a modular Lean F-section rule library for B/A/E, compose actual blank trace through many genuine sections **only if it contributes a reusable symbolic invariant**, avoiding meaningless finite prefixes.
2. Seek a universal blank-reachable word invariant for the D-start Cryptid, ideally exhaustive rules on arbitrary suffix tokens; prior outside @-d 2.7-million-section computational frontier dwarfs a short trace.
3. Explore exact halting-cylinder reachability and potential 3-adic conjugacy, or switch to another holdout if more fruitful. Prefer closure over trivial residue-exclusion tallies.
4. Check broadcasts/direct agent messages, coordinate with Agent25/32/31 to avoid duplicate work.
5. All claims of new BB(6) exact values or holdout decisions would be false; mathematical progress so far is symbolic theorem composition.

Early CI failed three times due actual fields and recursion orientation; successful runs after fixing proof obligations. Local Lean v4.36.0-rc2 reconstructed in `/tmp/lean/lean-4.36.0-rc2-linux/bin/lean`; local simple model mock in `/tmp/bb6a37/BridgeMock.lean` but real source CI is authoritative.

## New CI-certified results after first checkpoint (09:30 UTC)

- [WordReturns.lean](../../im-results/agent37-cryptid-model-bridge/WordReturns.lean) all-natural arbitrary interleaved token list `wordCode(ws)` made of `10` and `111` has exact original raw F-to-F return and independently exact implicit-blank-right suffix version `complete_A_word_nil`. Manual authentic-source CI [41417962868](https://github.com/FlareZ123/bb6/actions/runs/41417962868) checked arbitrary word explicit-zero; subsequent [41421031957](https://github.com/FlareZ123/bb6/actions/runs/41421031957) checked implicit blank `complete_A_word_nil`, axioms `[propext, Quot.sound]` only.
- [DoubleOneBranch.lean](../../im-results/agent37-cryptid-model-bridge/DoubleOneBranch.lean) complete raw A-side branch `preA (m+2) (1100 ys) -> F(1^(2m+5) 0 1^6 ys)` in precisely `2*(m+2)+16` steps universally for all m and suffix ys, with `two_one_front` 17-step macro into `sweepD m`, plus `complete_A_word_two_one` that composes with arbitrary `wordCode ws` and original F-prefix. Real-source successful [CI 41421031957](https://github.com/FlareZ123/bb6/actions/runs/41421031957), all final `[propext, Quot.sound]`, no `sorryAx`. Proof was originally a prohibitively expensive 17-step `simp`; split into short fixed 4,6,7 step transitions and rewrote expensive definitional raw-model coercion via proven `preA_embed_ab`. CrossModelBridge now has `transfer_nonF` as well as `transfer_f0`.
- Active discovery hypothesis: general `110(10)^q0` A-suffix has exact raw return with time `2*(m+2)+16+4*q` and outgoing `1^(2m+5) 0 1^(2q+6)` for m≥0, all q,ys. Independent small-case simulation and a complete first-stage symbolic Lean proof compiled locally in `/mnt/data/PairQMock.lean`, proving `q_front` after `17+4q` raw steps and using authentic raw transition semantics copied from Agent31. **Not yet source-certified or globally proved**; next steps port to original `Boundary` source in GitHub CI, compose with verified `sweepD_run`. All mock lemmas only standard axioms, but full authenticated theorem must be checked independently. Do not call a publishable new result until source verification.

The user has received durable progress responses for first three CI successes and source-checked 1100; no BB6 exact value. Respect lease release only on measured >= 09:56:28 UTC.
