# Exact primitive-step certificates for the two live F289 halting roots

**Scope:** two six-state, two-symbol machines whose halting was established by the pinned upstream Cryptids library. This dossier computes exact primitive-step counts and connects them to a higher-bound local frontier. It does not resolve a previously unknown halt/nonhalt decision or establish BB(6).

## Counts and evidence

| Blank-start machine (RLE) | Successful transitions | Score including final halt attempt |
|---|---:|---:|
| `1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LA---` | 932242535661307148726923126800831715518673957228 | 932242535661307148726923126800831715518673957229 |
| `1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RD---` | 111579188581812927653348117002306046024821208051411619955580898884568781 | 111579188581812927653348117002306046024821208051411619955580898884568782 |

Both numbers are independently reproduced by BigInt replay and Lean evaluation of the accelerated RLE states. All ten checkpoint cost equalities were accepted locally by the Lean kernel (4.36.0-rc2; `propext` only), and the pinned-source audit [45370740330](https://github.com/FlareZ123/bb6/actions/runs/45370740330) accepted the counted primitive rules for both machines. The full primitive-step certificate is still conditional on successful source compilation of the macro/dispatcher/concatenation proof. The corrected combined source audit is [45372456012](https://github.com/FlareZ123/bb6/actions/runs/45372456012).

These scores are less than $2^{160}$ and $2^{237}$ respectively; neither is a new champion candidate.

## Mathematics

Let the segment list be $S=((r_i,c_i))$, with weight $W(S)=\sum_i c_i(6r_i+26)$. Write $s=W(S)$, $b$ for the bottom zero count, $c$ for the initial zero count, and $q$ for a repetition count. The exact closed costs of the main contractions (successful ordinary transitions, zero charge for pure encoding changes) are:

| Contraction | Cost |
|---|---|
| DR0 bottom | $6k+14$ |
| DR0 bottom repeated zeros | $6kq+9q^2+9q$ |
| clean sweep | $6b+41+s$ |
| DR0 one | $6c+6b+46+s$ |
| DR0 zeros | $6q(c+b)+15q^2+35q+qs$ |
| RNIL one | $6c+6b+57+s$ |
| RNIL zero power | $6qb+16q^2+41q+qs$ |
| P1 one | $10r+6b+75+s$ |
| P1 power | $q(7r+50+6b+s)+(3r+25)q^2$ |
| P2 one | $15r^2+77r+73+6b(r+1)+(r+1)s$ |
| P2 power | $q(37r+48+6b(r+1)+(r+1)s)+(r+1)(15r+25)q^2$ |

The key is to sum the segment-dependent cost using its linear weight update under `pushSeg`, rather than expanding the immense tapes or using an upper bound for each contraction. [RleCostAlgebra.lean](RleCostAlgebra.lean) proves the recurrence identities and the weight update, by induction and polynomial normalization.

The counted relation `ReachesIn M n a b` specifies exactly n successful primitive steps of the original machine. The counted macros replace the upstream transitive-reachability lemmas with this indexed relation and reindex each sum by the proved arithmetic identities. `StateHaltsAt M s n` records exact successful moves remaining in an RLE state; when the compressed terminal flag is set, n is zero. The counted dispatcher propagates exact remaining-time certificates backward, and the chunk lemmas sum the finite batch costs before adding the initial primitive step. The final source bridge verifies the underlying ConjectureMachines iterator's last successful configuration and immediately following undefined transition.

## Reproducibility

* Pin upstream `google-deepmind/cryptids@3647718b5df22e1a61462dec0376bd204526285a`, Lean 4.36.0-rc2 and matching Mathlib.
* [RleCountedAtoms.lean](RleCountedAtoms.lean): original-source primitive rule proofs and machine-specific initial conditions.
* [RleCountedMacros.lean](RleCountedMacros.lean), [RleDispatchCosts.lean](RleDispatchCosts.lean), [RleCountedDispatch.lean](RleCountedDispatch.lean): uniform counted contractions and backward exact-halt theorem.
* [RleCountedRoots.lean](RleCountedRoots.lean): original checkpoint states, kernel-reducible cost equalities, exact root composition.
* [RleExactTransfer.lean](RleExactTransfer.lean): canonical source-machine step semantics.
* [RleCountedAll.lean](RleCountedAll.lean): combined audit source, after compiling RleCostAlgebra and RleCountedAtoms.
* [replay_exact_cost.js](replay_exact_cost.js), [exact-candidate-counts.json](exact-candidate-counts.json), [RleStandaloneCompute.lean](RleStandaloneCompute.lean): independent executable checks and exact candidate counts. Executable replay by itself does not prove the original machine's primitive cost.

## Global frontier integration

The locally kernel-checked [AuditRaiseBound.lean](AuditRaiseBound.lean) proves that changing an audit's predicate to a weaker one preserves every open leaf and the exact count report. This applies in particular to raising a primitive-score cutoff from 6 to $2^{237}$.

[RleCoverageGraft.lean](RleCoverageGraft.lean) and [RleFrontierGraft.lean](RleFrontierGraft.lean) are the source-dependent integration: transfer the two literal-machine scores into BB6Coverage, raise the existing six-root audit's bound, remove both singleton cylinders, prove exact residual open-set equivalence, and transfer exactly two units from open mass to certified mass. Their combined manual audit has been submitted using the existing shared source-audit workflow, with `verify_six_root_graft=true` and `verify_f289_exact_graft=true`. Until this succeeds, the exact leaf closure is not certified.

## Remaining obligation

Complete the source check and repair any remaining elaboration failures. If accepted, the two root certificates close two previously open *local frontier* leaves and strengthen the score-aware classification. All other open leaves remain, and the complete universal upper bound and champion exact score remain separate obligations.
