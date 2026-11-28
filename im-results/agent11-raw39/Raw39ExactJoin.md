# Raw39 exact weighted threshold — final two obligations

The corrected candidate for the entire Raw39 cylinder is **28311**, and an explicit normalized compatible halting completion attains that score unconditionally:
```
1RB1LE_1RC1LF_0RD1RB_1LD0RA_0LA0LB_---1RD
```
Here F0 is the genuine halt. There are 28309 ordinary transitions from A on blank, plus the halt attempt and one incoming blank delay (E0=0LA). The new `BB6.Agent43Raw39ExactJoin.parent_attained` proves existence with the exact weighted score, and `parent_not_bound` rules out 28310 for the whole parent.

For 0LE, `Raw390LELateWeight.lean` proves the exact leaf threshold and the child lower bound 15125, using the late leaf 9036:
```
1RB0LE_1RC0LA_0RD---_1LD0RA_1RA1LF_0LB1LF
```
The first hole C1 is reached at 15124; the halt refinement has possible incoming delays [0]. A focused direct replay of the 11603 existing open tables through 15130 finds exactly ten hole-reaching leaves and no weighted score greater than 15125. This numerical observation is not the full upper-bound proof.

`Raw39ExactJoin.lean` imports the checked nine-child composition, both exact lower-bound witnesses, and the monotonicity lemma. It proves:
- `parent_attained` and `parent_not_bound` unconditionally;
- `zeroLE_exact` given Bound 15125 for A1=0LE;
- `oneLE_exact` given Bound 28311 for A1=1LE;
- `parent_bound`, `parent_cover`, and `parent_exact` given precisely those two upper-bound hypotheses.

Local Lean 4.36.0-rc2 checks succeeded for all listed theorems with standard axioms [propext, Classical.choice, Quot.sound]. The exact nine accepted artifact closures plus 1LE g2 were merged, checking source/object hashes, duplicate identity and compiler version: 1594 distinct source/object pairs. Raw39AcceptedSix through Nine re-linked (no regeneration of child proofs); final join compiled in 1.85 seconds, peak RSS ~2.37 GB.

Source-audit status on 28 November:
- **0LE complete:** [46093979153](https://github.com/FlareZ123/bb6/actions/runs/46093979153) passed all eight shards and final Lean child closure at bound 15125.
- **1LE incomplete:** [46094272482](https://github.com/FlareZ123/bb6/actions/runs/46094272482) accepted individual shard jobs g0,g2,g3,g4,g6,g7, but g1's runner shut down and g5 exceeded the 45-minute limit. The replacement [46102161614](https://github.com/FlareZ123/bb6/actions/runs/46102161614) reuses those six corrected-bound artifact closures at pinned source revision e7c319dd, with sixteen smaller leaf groups for the missing source proof modules. It has not yet passed; a complete 1LE source audit is required.

The pending final joins are prepared as source candidates in `Raw39CompleteJoin.lean` and `Raw39Canonical40Bridge.lean`; the explicit roster40 membership preflight is `Raw39Canonical40Membership.lean`. These modules do not yet have combined original-source Lean acceptance. Do not decrement the global roster before both complete child bounds are actually accepted and the unconditional join consumed. No exact BB(6) assertion.
