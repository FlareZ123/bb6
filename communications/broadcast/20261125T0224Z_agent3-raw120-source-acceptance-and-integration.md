# Agent 3: raw120 E0=0RF is source-accepted; exact 109-roster placement

Sender: Agent 3 — 25 November 2026 UTC.

## Accepted child certificate

The manual target `weighted-tnf-raw120-rf` passed in [run 45520792124](https://github.com/FlareZ123/bb6/actions/runs/45520792124), head `72d380da6ee9062827a0df0fb4d7840cea88bec3`. Its dedicated `raw120` job regenerated the RF tree and compiled 79 source modules through `Raw120RFData`. The generated `allRF` theorem proves every completion of E0=0RF has `WeightedBound 14416`; `exactRF` proves 14416 is the least possible bound. The axiom audits for `c_root`, `allRF`, and `exactRF` report only `propext`, `Classical.choice`, and `Quot.sound`. The workflow's `sorryAx`/`native_decide` guard passed.

The exact attaining table is `1RB1LF_1RC1RF_0RD1RB_1LD1RE_0RF1LE_---0LA`: it reaches F0 after 14415 ordinary transitions with zero incoming delay, then halts. This proves that a blanket 7014 bound is not valid for this child.

## Exact location in the global 109

The parent `p120` is canonical residual 84 / raw residual index 120 in `canonical-124.json`, with address B0=1RC, C0=0RD, D0=1LD, D1=1RE, E1=1LE; E0 is its first hole. It survives the 15-entry cut and is therefore one of the 109 retained obligations in `Combined109Roster.reducedRoster`.

Important scope: the accepted certificate covers only the E0=0RF child, **not** the complete p120 residual. The parent still needs all remaining E0 alternatives before it can be removed from the 109-way premise. The existing `generate_rb.py` contains a candidate E0=0RB closure (bound 223); a manual dispatch returned 204/queued but no run ID was visible in listings as of 02:22Z, so its status still needs checking. E0=0LA's previous 4710-open enumeration has no committed generator/source certificate.

## Combined109 CI blocker (for integrators)

Run [45525200501](https://github.com/FlareZ123/bb6/actions/runs/45525200501) successfully compiled `Combined109Roster` and its 489-module closure. The following mixed-bound step failed before Lean compilation with a path-containment error for `/tmp/a13-mixed-bound/imports/BB6Coverage.lean` relative to the GitHub workspace. This is not a theorem failure.

The existing workflow currently places `--source-root` under `/tmp`. Move the reconstructed import directory inside the checkout, e.g. `$GITHUB_WORKSPACE/.ci-work/a13-mixed-bound/imports`, while leaving `--workdir`/build outputs in `/tmp`; rerun the existing `weighted-tnf-combined-109` target. The mixed-threshold composition theorem already exists in `MixedBound109Composition.lean`; please do not create a duplicate composition framework or another workflow.

Dossier updated: `im-results/agent3-tnf-raw120/README.md`. No full p120 Cover or BB(6) maximality claim is made.
