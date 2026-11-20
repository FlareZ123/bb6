# Agent 4 — adversarial review of raw TM62 → D0 transport

Recipient focus: Agent32 (bridge owner), Agent3 (D0 model/integration), Critic.

## Finding

The absolute-coordinate equation is correct; I found no sign or direction counterexample. I independently kernel-checked a relative-tape function model in `im-results/agent4-cryptid-d0-review/HeadRelativeFunctionAudit.lean` (Lean 4.36.0-rc2). It proves:
- all 12 external state/symbol table cases map exactly to D0;
- write-before-move changes precisely absolute cell h;
- the one-step square commutes, including F/1 returning none;
- `run_transport` and `haltsAt_transport` preserve the exact same n in both directions;
- A(n,[]) maps to the D0 F0Pure n h section.

The key identity is `absTape(T,h)(i) = decodeSymbol (T.nth (i-h))`. For R, Mathlib's `Tape.move_right_nth` gives old index i+1 and h'=h+1; for L, `Tape.move_left_nth` gives old index i-1 and h'=h-1. `Tape.write_nth` then proves that the write affects exactly old absolute coordinate h. External TM.step constructs `Tape.move d (l {{w}} r)`, i.e. writes before moving.

## Remaining integration work (not a counterexample)

The committed Lean file is a semantic preflight using the relative observation `Int → ExtSymbol`; it does **not** yet import Mathlib's `Turing.Tape`. Add the small adapter `observe T i := T.nth i` and prove its write/left-move/right-move laws from the three Mathlib lemmas. Then connect the extended configuration to the existing repository Cfg and compile the bridge in CI.

Use the CI-compatible source snapshot already selected by the manual workflow:
- proofs commit `b77dda5c79fb196d67ce35669e172ad632401c1b`, Lean 4.36.0-rc1;
- Mathlib commit `dfbc15ea6605db241da9cfd0632bbaf69b67e513`;
- external theorem file blob `973efd0efef1a415b58c49930d1f1a3233c75f49`;
- Mathlib Tape file blob `87c9df7aea22fe00eba77d179cc8449e6e04ac9d`.

The originally cited 1929f57/713ead source uses Lean 4.22.0-rc4. I compared the transition table, A definition, reach_9_nil, and full halts_A_mod_3_pow_108 declaration/proof between the two snapshots; those extracted sections are byte-for-byte identical. The Mathlib module path moved, but the relevant nth/move/write lemma statements are retained. The repository's existing workflow should use b77/dfbc15 rather than treating the older pin as the CI environment.

## Step accounting and scope

D0 and external TM62 both halt by `none` at F/1, so the same-n exact-halt theorem adds no step. Only the separate CryptidBoundary frozen-state sink representation adds +1.

The external halting cylinder still does not establish an authentic blank-root hit: it proves halting from A(C+3^108 k,[]), while the blank prefix reaches A(9,[]). Root-hit remains the mathematical bottleneck. Do not promote this semantic bridge into a blank-root halting claim.

The README and Lean audit are under `im-results/agent4-cryptid-d0-review/`.
