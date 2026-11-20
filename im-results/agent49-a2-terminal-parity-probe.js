// Targeted parity probe for the A=2 terminal diagnostic at z=1, L=3.
// Deterministic sparse tape; absent Map entries are blank.
// Run with Node.js: node agent49-a2-terminal-parity-probe.js

"use strict";

const TM = [
  [[1, 1, 1], null],
  [[1, -1, 2], [0, 1, 5]],
  [[1, 1, 4], [0, -1, 3]],
  [[0, -1, 2], [1, 1, 1]],
  [[1, 1, 0], [1, 1, 4]],
  [[1, 1, 4], [0, 1, 3]],
];

const z = 1;
const L = 3;
const limit = 20_000_000;
const D0 = [0, 0, 1];
const D1 = [1, 1, 1];
const MARKER0 = [0, 1];
const LH = [1, 1, 0, 1, 1, 1];

function repeat(block, n) {
  return Array.from({ length: n }, () => block).flat();
}

function bit(tape, x) {
  return tape.get(x) === 1 ? 1 : 0;
}

const m = 3 * 2 ** z + 3 * z + 7;
const n = 2 ** (2 ** z - 1);
const K = 2 ** z + z + 3;
const H = m + 2 + 3 * n;
const ell = [
  ...repeat(D1, K),
  ...MARKER0,
  ...repeat(D0, 2),
  ...repeat(D1, 2),
  ...repeat(D0, L + 1),
  ...LH,
];

// q4Tail-to-S0 frame output:
// s0Config ell (n-1) (2^(n-1)-1) 0 H.
// For z=1, n=2 and binDec(1,1)=d0.
const left = [...repeat(D0, n - 1), ...ell];
const right = [0, 1, 1, 1, 0, 0, ...D1];
const tape = new Map();
left.forEach((v, i) => { if (v === 1) tape.set(H - i, 1); });
right.forEach((v, i) => { if (v === 1) tape.set(H + 1 + i, 1); });

let state = 3;
let head = H;
let eventCount = 0;
const firstEvents = [];
const lastEvents = [];
let halt = null;

for (let steps = 0; steps < limit; steps++) {
  if (
    state === 4 &&
    head === 1 &&
    Array.from({ length: 8 }, (_, i) => bit(tape, -3 + i)).join("") === "11110000"
  ) {
    eventCount++;
    if (firstEvents.length < 5) firstEvents.push(steps);
    lastEvents.push(steps);
    if (lastEvents.length > 8) lastEvents.shift();
  }

  const transition = TM[state][bit(tape, head)];
  if (transition === null) {
    halt = { steps, state, head, read: bit(tape, head) };
    break;
  }

  const [write, move, nextState] = transition;
  if (write === 1) tape.set(head, 1);
  else tape.delete(head);
  head += move;
  state = nextState;
}

const terminalANumerator = 2 ** (L + 7) - 35;
const terminalAQuotient = Math.floor(terminalANumerator / 3);
const terminalARemainder = terminalANumerator % 3;

process.stdout.write(JSON.stringify({
  z, L, m, n, K, H, limit,
  eventCount, firstEvents, lastEvents,
  final: { state, head, ones: tape.size },
  halt,
  marker0TerminalA: {
    numerator: terminalANumerator,
    quotient: terminalAQuotient,
    remainder: terminalARemainder,
  },
}, null, 2) + "\n");
