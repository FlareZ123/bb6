# Initial S1 root witness (kernel-checked root bridge)

## Kernel-checked claim

Using the `tm2` transition table in `im-results/agent48-champion-root/ChampionRootBridge.lean` and the exact `fMove` marked-list update, a finite simulation from the blank configuration reaches the S1-encoder candidate

```lean
s1Config 3 7 2 6 0 63 29
```

after exactly **27,959 steps**. The finite output is state 3, head 29, with the marked-list order

```lean
[31, 32, 33] ++
  (List.range 192).map (fun i => (36 + i : Int)) ++
  (List.range 18).map (fun i => (29 - i : Int)) ++
  [11, 10, 8, 5, 2, -1, -4, -5, -6, -8, -9, -10]
```

The support has 225 cells. It matches the S1Encoder decomposition:
- `d1pow 6` at the head-facing positions 29 down to 12;
- marker m2 at 11, 10, and 8;
- the separate d0 delimiter at 5;
- `binDec 3 7 = d0 ++ d0 ++ d0`, contributing 2, -1, -4;
- `lh`, contributing -5, -6, -8, -9, -10;
- the right RC prefix at 31, 32, 33 and `d1pow 64` at 36 through 227.

This is now a kernel-checked Lean theorem, not merely a simulation checkpoint. `im-results/agent48-root-witness/RootFiniteBits.lean` proves the exact 27,959-step run using a 238-cell Nat-bitset and proves its soundness against the infinite-tape semantics. `RootSourceBridge.lean` proves exact equality with the unchanged S1Encoder definition and establishes `run tm2 27959 blank = some (s1Config 3 7 2 6 0 63 29)`. The final theorem reports only `[propext, Quot.sound]`, with no `sorryAx` or `native_decide`. The JS reproducer below remains an independent cross-check; the Lean proof is authoritative. See [the proof dossier](../agent48-root-witness/README.md).

## Root-offset cross-check

The same finite simulation gives:
- from blank state 0: after 9 steps, state 4, head 3, marks `[2,0,-1,-2]`;
- from blank state 4: after 15 steps, the identical finite configuration.

It then reaches the S1 candidate after 27,959 steps from state 0, or 27,965 steps from blank state 4. This agrees with `join_source` in `ChampionRootBridge`, which identifies the 9-step and 15-step root offsets.

## Reproduction

The following JavaScript uses the same six-state table and list update as `tm2`/`fMove`:

```js
const transitions = [
  [[1, 1, 1], null],
  [[1, 0, 2], [0, 1, 5]],
  [[1, 1, 4], [0, 0, 3]],
  [[0, 0, 2], [1, 1, 1]],
  [[1, 1, 0], [1, 1, 4]],
  [[1, 1, 4], [0, 1, 3]]
];

let state = 0, head = 0, marked = [], steps = 0;
while (steps < 27959) {
  const t = transitions[state][marked.includes(head) ? 1 : 0];
  if (!t) throw new Error(`halted at ${steps}`);
  const [write, right, next] = t;
  marked = write
    ? [head, ...marked.filter(x => x !== head)]
    : marked.filter(x => x !== head);
  head += right ? 1 : -1;
  state = next;
  steps++;
}
({ steps, state, head, marked });
```

The simulation should return `steps=27959`, `state=3`, `head=29`, and the 225-cell list above. This is independent of the Lean proof state; it should be used as a checkpoint for formalization, not as a substitute for the theorem.
