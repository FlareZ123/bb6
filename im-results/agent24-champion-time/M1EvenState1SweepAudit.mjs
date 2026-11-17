// Reproduce the M1-even state-1 sweep precondition audit.
// Exact TM2 table and S1Encoder block conventions; finite simulation only.
const d0 = [false, false, true];
const d1 = [true, true, true];
const lh = [true, true, false, true, true, true];
const markerWord = m => m % 3 === 0 ? [false, true]
  : m % 3 === 1 ? [true, false, true] : [true, true, false, true];
const d1pow = n => Array.from({ length: n }, () => d1).flat();

function binDec(len, n) {
  let p = 2 ** (len + 1) - 1 - n;
  const out = [];
  for (let i = 0; i < len; i++) {
    if (p <= 1) break;
    out.push(...(p % 2 === 0 ? d0 : d1));
    p = Math.floor(p / 2);
  }
  return out;
}

// Each entry is [write, head displacement, next state].
const tm2 = [
  [[true, 1, 1], null],
  [[true, -1, 2], [false, 1, 5]],
  [[true, 1, 4], [false, -1, 3]],
  [[false, -1, 2], [true, 1, 1]],
  [[true, 1, 0], [true, 1, 4]],
  [[true, 1, 4], [false, 1, 3]],
];

function startS1(L, n, m, a, b) {
  const left = [...d1pow(a), ...markerWord(m), ...d0, ...binDec(L, n), ...lh];
  const right = [false, true, true, true, false, false, ...d1pow(b + 1)];
  const tape = new Map();
  left.forEach((bit, i) => tape.set(-i, bit));
  right.forEach((bit, i) => tape.set(i + 1, bit));
  return { state: 3, head: 0, tape };
}

function run(c, steps) {
  let { state, head, tape } = c;
  for (let i = 0; i < steps; i++) {
    const tr = tm2[state][tape.get(head) ? 1 : 0];
    if (tr === null) return { state, head, tape, stoppedAt: i };
    const [write, delta, next] = tr;
    tape.set(head, write);
    state = next;
    head += delta;
  }
  return { state, head, tape };
}

function v2(n) {
  let k = 0;
  while (n % 2 === 0) { n /= 2; k++; }
  return k;
}

function consecutiveLeftOnes(c) {
  let n = 0;
  while (c.tape.get(c.head - 1 - n) === true) n++;
  return n;
}

const rows = [1, 3, 5, 10, 20].map(a => {
  const L = 16, n = 32, b = 0, v = v2(n);
  const initial = run(startS1(L, n, 1, a, b), 12 * a + 6);
  const ones = consecutiveLeftOnes(initial);
  const required = 4 * (v - 1) + 1; // n cycles require n+1 ones
  const full = run(startS1(L, n, 1, a, b), 12 * a + 12 * v + 32);
  return {
    a,
    initialSteps: 12 * a + 6,
    initialState: initial.state,
    initialHead: initial.head,
    blankUnderHead: initial.tape.get(initial.head) === false,
    consecutiveOnesLeft: ones,
    onesRequiredForProposedSweep: required,
    proposedSweepPremiseHolds: initial.state === 1 &&
      initial.tape.get(initial.head) === false && ones >= required,
    fullPrefixSteps: 12 * a + 12 * v + 32,
    fullPrefixEndpoint: [full.state, full.head],
  };
});
console.log(JSON.stringify(rows, null, 2));
