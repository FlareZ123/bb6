// Independent deterministic replay of CountedResetBase's three local traces.
// The ordered marked-cell arrays intentionally match FConfig.fMove's list
// insertion/filter semantics; sorting them would make FConfig equality false.

const TM2 = [
  [[true, true, 1], null],
  [[true, false, 2], [false, true, 5]],
  [[true, true, 4], [false, false, 3]],
  [[false, false, 2], [true, true, 1]],
  [[true, true, 0], [true, true, 4]],
  [[true, true, 4], [false, true, 3]],
];

const inputs = [
  [-7, -4, -1, 2, 3, 4, 7, 8, 9],
  [-8, -5, -2, 0, 2, 3, 4, 7, 8, 9],
  [-6, -3, -1, 0, 2, 3, 4, 7, 8, 9],
];

const expected = [
  [7, 8, 9, 12, 13, 14, 5, 4, 3, 2, 1, -1, -4, -5, -6, -7],
  [7, 8, 9, 12, 13, 14, 5, 4, 3, 2, 1, 0, -2, -5, -6, -7, -8],
  [7, 8, 9, 12, 13, 14, 5, 4, 3, 2, 1, 0, -1, -3, -6, -7, -8],
];

function runBase(m) {
  let marked = inputs[m].slice();
  let state = 3;
  let head = 0;
  const steps = 63 + 4 * m;

  for (let k = 0; k < steps; k++) {
    const read = marked.includes(head);
    const transition = TM2[state][read ? 1 : 0];
    if (transition === null) {
      throw new Error(`unexpected halt at m=${m}, step=${k}`);
    }
    const [write, right, next] = transition;
    marked = marked.filter((x) => x !== head);
    if (write) marked.unshift(head);
    head += right ? 1 : -1;
    state = next;
  }
  return { state, head, marked };
}

for (let m = 0; m < 3; m++) {
  const got = runBase(m);
  const want = expected[m];
  if (got.state !== 3 || got.head !== 5 ||
      JSON.stringify(got.marked) !== JSON.stringify(want)) {
    throw new Error(`m=${m}: mismatch: ${JSON.stringify(got)}`);
  }
  console.log(`m=${m}, steps=${63 + 4*m}, state=${got.state}, head=${got.head}, marked=[${got.marked.join(",")}]`);
}
