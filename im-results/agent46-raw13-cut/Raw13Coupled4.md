# Four-hole extension of Raw13 #1093

**Exact weighted threshold 62,123, accepted conditionally in [CI 45949046313](https://github.com/FlareZ123/bb6/actions/runs/45949046313).** The single premise is the independently source-verified `NeverHalts published` lemma from the three-hole branch. The literal four-hole table is `1RB1LD1RC---1LA1RE1LF0LA---0RD------`. Its F0=1LC branch has an unconditional exact weighted threshold 134 by original-source transport in [CI 45937489536](https://github.com/FlareZ123/bb6/actions/runs/45937489536), artifact 15171802953. The four-hole cut retains a parameter for that theorem so that it can first compile without rebuilding the external Cryptids project.

The remaining F0 branches yielded 62 difficult literal one-hole tables in the original scan. The [saved discovery bank](coupled4-candidates.json), CI [45937223189](https://github.com/FlareZ123/bb6/actions/runs/45937223189), contains six FAR witnesses, 44 positive-cost affine sweep candidates, one finite halt and eleven unresolved entries. The finite halt is at first missing query time 62,122, hence 62,123 including the halt:

`1RB1LD_1RC0RB_1LA1RE_1LF0LA_1LA0RD_1LE---`.

Every zero row writes 1, so the witness's incoming zero-write delay is zero. The former finite maximum 629 is superseded. The other 61 difficult leaves surviving two million steps does not prove nonhalting.

## Cross-parent abstraction transfer

The eleven remaining exact tables were tested with Agent25's periodic word deletion/residue generator (symmetric parameters, window lengths 8–24, periods from 1 through 12, cutoffs/moduli 1–3; cap 10,000 abstract configurations), followed on four failures by Agent19's lag-XOR/rungram summary (lag 2 sufficed, cap 10,000). Seven succeeded in the first portfolio; all four others succeeded in the second. Their exact compact DFA transitions, parameters, state and edge counts are saved in [coupled4-bidfa.json](coupled4-bidfa.json), with [deterministic replay](replayCoupled4BiDFA.js). The state counts in literal roster order are 397, 375, 235, 235, 962, 649, 108, 1563, 110, 828, 418. All eleven literal nonhalting theorems were accepted by Lean, and the full parent certificate has been accepted.

The earlier hand-written stride-three counter theorem has standard-axiom output in CI 45938170222; that overall job failed on directed transfer and nested-sweep elaboration. The new generator does not depend on those auxiliary candidates. It reconstructs each DFA fixed point using Agent32's independent `emit_rungram.py`, emits rowwise FastBiDFA checks and supplies the resulting `NeverHalts` to the exact literal parent certificate. It retains the 44 prior affine fixtures, six prior FAR witnesses, chunked finite halt certificate and accepted 134-threshold graft.

The generated `Raw13Coupled4` exports `empty_complement`, `bound`, `bound_quotient`, and `exact_threshold`. The halting trace is verified in 512-step chunks with balanced composition and explicit arithmetic equalities; the attaining witness compatibility is proved by a finite pointwise check. All exported proof axiom profiles are standard. No reduction of the global canonical roster is asserted here.
