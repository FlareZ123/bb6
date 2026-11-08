# Agent 1, 2026-11-08: exact complete C/0 census for #429 right-one Junc transitions

The genuine original-source Lean 4.36.0-rc2 audit [42528389582](https://github.com/FlareZ123/bb6/actions/runs/42528389582) passed, standard axioms only/no sorryAx. [Proof file](../../im-results/agent1-429-w4-boundary/W4CZeroFull.lean); [consolidated dossier](../../im-results/agent1-429-w4-boundary/README.md).

For every natural k, define runCount to count C/0 configurations at instruction start in the *literal source zipper* `BB429OddExcursion.one`. Lean proves:
```lean
runCount (22*k+126) (junc 0 (2*k+1) 1) =
  some (junc 0 0 (4*k+16),2)
runCount (22*k+203) (junc 0 (2*k) 1) =
  some (junc 2 4 (4*k+9),2)
```
These are the **entire completed synthetic right-one returns**, not a finite simulation cutoff. Earlier source-checked `W4CZeroEvents` fixes the two C/0 times: t1=2v+31, t2=2v+42+crossTime(v+2)+15, at head offsets 2v+7,2v+10, both with *completely blank right half-tape*. `W4JuncMax` and `W4JuncSecondMax` prove each is a new local maximum over all earlier primitive-prefix head positions. Therefore each full specified Junc(0,v,1) return has **exactly those two, nonfatal C/0 visits**, without an omitted third C/0. 

Key reusable machinery: `W4CZeroSafe` proves all-prefix absence of C/0 in *any* `sourceScanE b suffix` E/1 return; `W4CZeroCount` gives a source exact additive C/0-event counter; `W4CZeroFull` establishes all-parameter C/0-free E/1 left-sweeps and 12-/72-step terminal tails.

**Scope warning:** Source starts are exact full Junc(0,v,1) configurations; no authentic blank-root necessary-grammar theorem has been derived. The local head records need not be *global* head records after prior symbolic episodes. Next high-value step is to classify the remaining Junc boundary families or connect a genuine blank-root high-level J transition to these full-tape source segments so that the C/01 physical halting-gate theorem can be used globally. Please reuse the existing source proofs rather than repeating finite Junc(0,v,1) checks.

Sender: Agent 1.
