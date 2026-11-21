# D0 authentic-root A-section trace (intermediate computational evidence)

**Status:** exact sparse-tape simulation, not a Lean theorem. This is an independent diagnostic for the authentic root-reachability problem; it does not prove halting or nonhalting.

## Setup

The transition table is copied cell-for-cell from `BB6.Portfolio.D0` in `im-results/agent3-portfolio-raw-conjugacy/DTableWitness.lean`, with A–F encoded as 0–5 and symbols 0/1. The starting section is external `A(9, [])`: state F (5), head 0, ones exactly at positions 1 through 9, and blank elsewhere. The repository's existing blank-root prefix is 36 raw transitions to this section with absolute head -6.

A section `A(n, ls)` is recognized exactly when:
- state is F;
- the scanned cell is blank;
- no one lies at or left of the head;
- the right tape has a maximal initial run of n ones;
- `ls` is the finite bit suffix beginning with the first blank after that run and ending at the last one (trailing blanks omitted).

The simulator stores only one-cells in a `Set`; writes and head moves are exact, with no bounded tape window.

## Observed sections

Primitive times below are measured from `A(9, [])`; add 36 to obtain times from the blank root. Relative head coordinates are measured from the head of `A(9, [])`; subtract 6 to obtain absolute root coordinates.

| Relative primitive time | Relative head | Section |
|---:|---:|---|
| 0 | 0 | `A(9, [])` |
| 190 | -16 | `A(27, [])` |
| 1,394 | -62 | `A(75, [])` |
| 9,526 | -188 | `A(203, [])` |
| 66,717 | -529 | `A(545, [])` |
| 468,758 | -1,440 | `A(1457, [])` |
| 3,315,263 | -3,871 | `A(3889, [])` |
| 23,503,068 | -10,352 | `A(10365, [0,1,1,1,1,1,1])` |
| 166,999,700 | -27,638 | `A(27659, [])` |

The eighth section is important: after the empty-suffix sequence reaches `A(3889, [])`, the next section has a nonempty seven-bit suffix `0111111`; that suffix is later consumed before the following empty-suffix section. Thus a return map on n alone is insufficient. The first six empty-suffix updates happen to fit `n=3q -> 8q+3` and `n=3q+2 -> 8q+9`, but this must not be extrapolated across the suffix excursion. In particular, applying the suffix-free formula to 10365 would predict 27643, whereas the actual next empty-suffix section is 27659.

The corresponding blank-root absolute times are 36, 226, 1,430, 9,562, 66,753, 468,794, 3,315,299, 23,503,104, and 166,999,736. The corresponding absolute head coordinates are -6, -22, -68, -194, -535, -1,446, -3,877, -10,358, and -27,644.

## Reproduction

Save the following as `root_section_trace.js` and run with Node.js. Default horizon is 300,000,000 primitive steps; pass a different maximum as the first argument.

```js
const tm = [
  [[1, 1, 1], [0, 1, 4]],
  [[1, -1, 2], [0, 1, 0]],
  [[1, -1, 0], [1, -1, 3]],
  [[1, -1, 2], [1, -1, 5]],
  [[0, -1, 2], [0, -1, 1]],
  [[1, -1, 4], null]
];

function trace(initialN, maxSteps) {
  const ones = new Set(Array.from({ length: initialN }, (_, i) => i + 1));
  let min = 1, max = initialN;
  let state = 5, head = 0, steps = 0;
  const sections = [];

  function write(pos, bit) {
    if (bit) {
      if (!ones.has(pos)) {
        ones.add(pos);
        if (pos < min) min = pos;
        if (pos > max) max = pos;
      }
    } else if (ones.delete(pos)) {
      if (ones.size === 0) {
        min = Infinity;
        max = -Infinity;
      } else {
        if (pos === min) do { min++; } while (!ones.has(min));
        if (pos === max) do { max--; } while (!ones.has(max));
      }
    }
  }

  while (steps < maxSteps) {
    if (state === 5 && !ones.has(head) && min >= head + 1) {
      let n = 0;
      while (ones.has(head + 1 + n)) n++;
      const suffixStart = head + n + 1;
      const suffixOnes = [];
      if (max >= suffixStart) {
        for (const pos of ones) if (pos >= suffixStart) suffixOnes.push(pos - suffixStart);
      }
      suffixOnes.sort((a, b) => a - b);
      const suffixLen = max >= suffixStart ? max - suffixStart + 1 : 0;
      sections.push({ steps, head, n, suffixLen, suffixOnes });
    }

    const bit = ones.has(head) ? 1 : 0;
    const instruction = tm[state][bit];
    if (instruction === null) return { halted: true, steps, sections };

    const [newBit, direction, nextState] = instruction;
    write(head, newBit);
    head += direction;
    state = nextState;
    steps++;
  }
  return { halted: false, steps, head, state, ones: ones.size, sections };
}

const maxSteps = Number(process.argv[2] ?? 300000000);
console.log(JSON.stringify(trace(9, maxSteps), null, 2));
```

## Cross-check against the DRegular source-section model

Under the repository's exact section encoding `ASection(a,r)=init(replicate (a-2) true ++ r)` and `regularSuffix(L(a,q,b))=(01)^q1^b`, the nine observed sections are exactly the first eight DRegular states:

`L(9,0,0) -> L(27,0,0) -> L(75,0,0) -> L(203,0,0) -> L(545,0,0) -> L(1457,0,0) -> L(3889,0,0) -> L(10365,1,5) -> L(27659,0,0)`.

In particular, `(01)^1 1^5 = 0111111`, so the nonempty suffix observed at the eighth section is exactly the DRegular `(q,b)=(1,5)` state, and the next raw return consumes it to `(0,0)`. This is an independent raw-table simulation cross-check of the first eight arithmetic section transitions and their physical endpoints; it is not a replacement for the existing Lean source-contract proof. The cumulative observed duration from `A(9,[])` to `L(27659,0,0)` is 166,999,700 primitive steps. Compare this with `DRegular.accumulated 8 (⟨9,0,0⟩)` when the archived source module is available.

## Interpretation and next mathematical task

This trace is useful for checking the initial raw-machine section path against the source-certified DRegular return model. It does not cover the later 2,640th DRegular state or the 108-level halting cylinder. The next useful result is a universal, source-certified section transducer that tracks both the unary parameter and the suffix, then compares the authentic root itinerary with the external halting-cylinder checkpoints. A scalar recurrence in n alone is demonstrably inadequate.

Keep this artifact in `im-results/`; it is not a publishable BB(6) result.
