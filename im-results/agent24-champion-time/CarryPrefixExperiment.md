# TM63 binary-carry prefix: arbitrary-run experiment

Status: **deterministic simulator evidence for r=1..5; only r=1 is presently Lean-proved.** This is an intermediate result, not a publishable theorem.

## Question

The pinned TM63 source has binary-counter blocks d0 = [1,0,0] and d1 = [1,1,1]. The local decrement carry word for a positive argument with 2-adic valuation r is d0 ++ d1^r, and its target is d1 ++ d0^r.

The existing counted local modules give:
- r=0: `counted_odd_counter`, cost 48+12c.
- r=1: `even_counted_odd_counter`, cost 60+12c.

The second theorem's 27-step prefix (`even_prefix15`, despite its name) is the exact r=1 instance of the following observed family.

## Candidate prefix theorem

For r ≥ 1, start TM63 in state D (state 3), head 0, with marked cells

`{-3r-2} ∪ {x | -3r+1 ≤ x ≤ 0} ∪ {2,3,4}`.

Thus the binary prefix is d0 d1^r, ending at the head; the fixed right-side marks are at 2,3,4. The simulator reaches state E (state 4), head 7, after exactly

`15 + 12*r`

steps. The output marked cells are

`{-3r-2, -3r-1, -3r} ∪ {-3r-2+3j | 1 ≤ j ≤ r} ∪ {1,2,3,4,6}`.

The binary prefix in that output is exactly d1 d0^r. For r=1, this is the checked `even_prefix15` trace:
- input marks: `[-5,-2,-1,0,2,3,4]`;
- output marks: `[-5,-4,-3,-2,1,2,3,4,6]`;
- cost: 27.

## Reproduced finite simulation

The following standalone JavaScript uses the exact 12-entry TM63 transition table in `im-results/agent48-champion-root/ChampionRootBridge.lean`. A transition is `[writeBit, moveRight, nextState]`; `null` is halting.

```javascript
const table = {
  0: {0:[1,1,1], 1:null},
  1: {0:[1,0,2], 1:[0,1,5]},
  2: {0:[1,1,4], 1:[0,0,3]},
  3: {0:[0,0,2], 1:[1,1,1]},
  4: {0:[1,1,0], 1:[1,1,4]},
  5: {0:[1,1,4], 1:[0,1,3]}
};

function simulate(r, max=2000) {
  const tape = new Set([
    -3*r-2,
    ...Array.from({length: 3*r}, (_,i) => -3*r+1+i),
    2, 3, 4
  ]);
  let q = 3, h = 0;
  for (let t=0; t<=max; t++) {
    if (q===4 && h===7) {
      return {r, steps:t, state:q, head:h,
        marks:[...tape].sort((a,b)=>a-b)};
    }
    const tr = table[q][tape.has(h) ? 1 : 0];
    if (!tr) return {r, steps:t, halted:true, state:q, head:h};
    const [write, right, next] = tr;
    if (write) tape.add(h); else tape.delete(h);
    h += right ? 1 : -1;
    q = next;
  }
  return {r, timeout:true, state:q, head:h};
}

for (let r=1; r<=5; r++) console.log(simulate(r));
```

Observed first-hit results:

| r | steps | output marks |
|---:|---:|---|
| 1 | 27 | -5,-4,-3,-2,1,2,3,4,6 |
| 2 | 39 | -8,-7,-6,-5,-2,1,2,3,4,6 |
| 3 | 51 | -11,-10,-9,-8,-5,-2,1,2,3,4,6 |
| 4 | 63 | -14,-13,-12,-11,-8,-5,-2,1,2,3,4,6 |
| 5 | 75 | -17,-16,-15,-14,-11,-8,-5,-2,1,2,3,4,6 |

These agree with the candidate output formula and `15+12r`. The r=1 case is independently established by the Lean theorem; r=2..5 remain simulation only.

## What this would imply, and what it does not

The common right-unary suffix in `CountedOneZeroUnary.lean` costs

`3(c+1) + 4 + 3(5+3c) + 11 = 33+12c`.

If the candidate prefix theorem is proved for arbitrary r ≥ 1 with a frame that preserves the exterior tape, the same suffix would give

`(15+12r) + (33+12c) = 48+12r+12c`.

That is the proposed positive-valuation local micro-cost. It is **not yet a theorem**: the missing work is an induction proving the prefix family and its exact frame/exterior conditions, then composing it with the right-unary suffix and the published S1/BinDec encoder. The r=0 odd template remains a separate proved case.

The intermediate head/state snapshots show a nontrivial tail: for r=2 the 12-step boundaries are (D,0), (D,-4), (D,-2), (A,4), then (E,7); for r=3 they are (D,0), (D,-4), (D,-8), (D,-2), (A,4), (E,7); for r=4 they are (D,0), (D,-4), (D,-8), (D,-12), (D,-2), (A,4), (E,7); for r=5 they are (D,0), (D,-4), (D,-8), (D,-12), (A,-14), (D,-2), (A,4), (E,7). Do not assume a naive identical 12-step loop without proving the parity-dependent terminal phase.
