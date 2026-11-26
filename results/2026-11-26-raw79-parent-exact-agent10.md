# Raw79 exact weighted maximum: 2,354

**Theorem.** For the exact five-hole partial table `1RB---_1RC1LE_0RD---_1LD1RE_---0LB_------`, every compatible machine satisfies `WeightedBound 2354`, and this bound is sharp. The total completion `1RB0LF_1RC1LE_0RD0RB_1LD1RE_0LA0LB_0REHHH` executes 2,351 ordinary moves before the F1 halt query. Its admissible incoming blank delay is two (F0→E0→A0); the total is 2,351 + 1 + 2 = 2,354.

The parent has five holes, with 25^5 = 9,765,625 physical completions. The regenerated audit tree has 1,163 split nodes including root, 20,820 side-cycle leaves, 4,788 initial last-hole leaves, and 1,142 originally open leaves. The latter divide into 1,104 FAR certificates, 27 one-block sweeps, three two-block sweeps, two long-epoch sweeps, two explicit recursive growth certificates, and four later exact halts. The open-list SHA-256 is `362a4b61cde3ae936f499b3a4bcfdee58a3b8b970213d7aab543e882fbeee11a`. In particular the discovery cutoff 1,000 does not constrain the mathematical theorem: the last-halt certificate at move 2,351 supplies the attaining run.

## Proof acceptance

All shared original Lean source dependencies were recovered from the Raw106 source-only export, run [45746231446](https://github.com/FlareZ123/bb6/actions/runs/45746231446), artifact 15082864386, source revision `d4f8af6c95aa037f2a1a195301471bdacb1c78c2`. No imports were mocked. The already verified shared modules were reused. The original `Raw79Recursive.lean` and the locally regenerated `Raw79Pumps`, `Raw79Base`, 24 `Raw79Kid` branches and `Raw79Data` all compiled using Lean 4.36.0-rc2. The literal-parent equality, attainer, delay and exact threshold in [Raw79Attainment.lean](../im-results/agent10-tnf-multipump/Raw79Attainment.lean) and [Raw79ParentCover.lean](../im-results/agent10-tnf-multipump/Raw79ParentCover.lean) compiled as well. Every exported theorem has only standard axioms; in particular `tree79_checked`, `all79`, `parent_cover`, `literal_cover` and `exact_weighted_threshold` report [propext, Classical.choice, Quot.sound]. This is original-source local kernel acceptance, not a newly successful hosted CI job.

Regenerate candidate tree using the deterministic `enumerate.cpp` from [agent2-tnf-raw99](../im-results/agent2-tnf-raw99/) (Git blob `def9aa306cad7e6bd2b7abc4ff3ad7d741525517`), the exact parent above, and pinned witness indices from [specs.json](../im-results/agent10-tnf-multipump/specs.json). The local generator uses the same candidate discovery, sweep and masks algorithms and a chunk size of 96; source text formatting need not be byte-identical to the repository generator. The split count in the local proof includes the root (the earlier README figure 1,164 is not the count of this regenerated tree). All generated proof claims, including every recursive nonhalting certificate, are discharged by Lean, not the enumerator. 

The attainer uses `zipRead_eq` and `first_hole_halts`, avoiding the expensive naïve functional tape reduction for the 2,351-step trace. The two-step delay is independently decided in Lean.

## Scope

This closes the entire Raw79 cylinder and determines its weighted maximum. Exact membership and composition into the active canonical quotient roster remain separate obligations; no change in the accepted global residual count or exact BB(6) claim follows from this result alone.
