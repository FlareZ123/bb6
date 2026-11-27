# Raw residual 99: source-accepted exact weighted TNF bound

Parent `1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---0RE`, raw index 99 / canonical index 64 in Agent13's canonical 124-roster. All 25^4=390625 completions. Initial hole F0 after 17 ordinary moves. Exact maximum weighted score 196, witnessed by `1RB0RD_1RC1LF_0RDHHH_1LD1RE_1RB0LB_1LA0RE` (195 ordinary moves, halt query, zero incoming delay).

Compiled deterministic enumeration partitions the cylinder into 165 split nodes, 850 last-hole nodes, 2649 translated side-cycle leaves, and 297 further leaves. FAR search gives 287 certificates; remaining ten all have one hole and symbolic growing sweep certificates. Nine use Agent50's BlockPump; one uses Raw99Pad, proving physical invariance under a single trailing false in the left zipper list. The algorithm never promotes a timeout to a verdict.

Run `python im-results/agent2-tnf-raw99/generate.py` to compile the candidate generator, reproduce the tree, reconstruct FAR masks, and emit Lean modules. Run the existing agent13 coverage workflow with target weighted-tnf-raw99. The original source closure checks every branch using `ThreeHoleAudit`, all pump witnesses, the 196 bound and its attaining completion. Raw99RosterBridge attempts the integrated reduction 124 -> 123 with unchanged global residual bound 395. Generated files are ephemeral, compact witnesses and deterministic generator are committed.

**Status:** full original-source proof accepted in [run 45926296755](https://github.com/FlareZ123/bb6/actions/runs/45926296755), artifact 15166288975. The repaired padding lemma and all 76 modules compiled with Lean 4.36.0-rc2. `BB6.Agent2Raw99.exact99` proves the sharp threshold 196. The [four-parent union theorem](../../results/2026-11-27-four-sharp-parent-union-agent32.md) composes this with Raw95, Raw103 and Raw105. Global roster membership and composition remain separate obligations.

FAR code and certificate checker from Agent7; split/last/side interface from Agent31; symbolic zipper and pump semantics from Agent50; pure residual projection from Agent44. Generator requires the repository's existing source modules.
