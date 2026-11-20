// Deterministic sparse-tape replay of the z=1, A=2 TM63 terminal branch.
// No finite tape boundary: absent Map entries are blank (0).
// Run with Node.js: node a2_terminal_basecase_z1.js

"use strict";

const TM = [
  [[1,  1, 1], null],       // q0: 0 -> 1,R,q1; 1 -> halt
  [[1, -1, 2], [0,  1, 5]],
  [[1,  1, 4], [0, -1, 3]],
  [[0, -1, 2], [1,  1, 1]],
  [[1,  1, 0], [1,  1, 4]],
  [[1,  1, 4], [0,  1, 3]],
];

const D0 = [0, 0, 1];
const D1 = [1, 1, 1];
const MARKER0 = [0, 1];
const LH = [1, 1, 0, 1, 1, 1];
const RIGHT_TERMINAL = [0, 1, 1, 1, 0, 0, 1];

function repeat(block, n) {
  return Array.from({ length: n }, () => block).flat();
}

function bit(tape, x) {
  return tape.get(x) === 1 ? 1 : 0;
}

function sectionBits(tape, head, a, L) {
  const left = [
    ...repeat(D1, a),
    ...MARKER0,
    ...D0,
    ...repeat(D1, L),
    ...LH,
  ];
  for (let i = 0; i < left.length; i++) {
    if (bit(tape, head - i) !== left[i]) return false;
  }
  for (let i = 0; i < RIGHT_TERMINAL.length; i++) {
    if (bit(tape, head + 1 + i) !== RIGHT_TERMINAL[i]) return false;
  }
  return true;
}

function runCase(L, limit) {
  if (![2, 4, 6].includes(L)) {
    throw new Error("This diagnostic is intentionally restricted to L=2,4,6");
  }

  // z=1 gives m=16, n=2, K=6, H=m+2+3n=24.
  // A=2 residual: d1^K ++ 01 ++ d0^2 ++ d1^2 ++ d0^(L+1) ++ lh.
  const H = 24;
  const ell = [
    ...repeat(D1, 6),
    ...MARKER0,
    ...repeat(D0, 2),
    ...repeat(D1, 2),
    ...repeat(D0, L + 1),
    ...LH,
  ];

  // s0Config ell 1 1 0 H:
  // left-facing binDec(1,1) = d0, right-facing s0RightFacing(0)=011100111.
  const left = [...D0, ...ell];
  const right = [0, 1, 1, 1, 0, 0, ...D1];
  const tape = new Map();
  left.forEach((v, i) => { if (v === 1) tape.set(H - i, 1); });
  right.forEach((v, i) => { if (v === 1) tape.set(H + 1 + i, 1); });

  const terminalL = L + 4;
  const terminalA = (2 ** (L + 7) - 35) / 3;
  const N = 2 ** (L + 4) - 7;
  const predictedPrefix = 16 * N * N + 194 * N - 12 * L + 24;
  const terminalCost = 59 + 12 * (terminalL + terminalA);

  let state = 3;
  let head = H;
  let terminal = null;
  let halt = null;
  let eventCount = 0;
  const firstEvents = [];
  const lastEvents = [];

  for (let steps = 0; steps < limit; steps++) {
    if (
      state === 4 &&
      head === 1 &&
      Array.from({ length: 8 }, (_, i) => bit(tape, -3 + i)).join("") === "11110000"
    ) {
      eventCount++;
      if (firstEvents.length < 4) firstEvents.push(steps);
      lastEvents.push(steps);
      if (lastEvents.length > 3) lastEvents.shift();
    }

    if (!terminal && state === 3 && sectionBits(tape, head, terminalA, terminalL)) {
      terminal = { steps, head, a: terminalA, L: terminalL };
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

  const expectedEvents = 2 ** (L + 3) - 4;
  const expectedHead = 2 ** (L + 7) - 32;
  const expectedHalt = predictedPrefix + terminalCost;

  if (!terminal || !halt) throw new Error("Did not reach terminal section and halt within limit");
  if (terminal.steps !== predictedPrefix) throw new Error("Prefix-step formula mismatch");
  if (terminal.head !== expectedHead) throw new Error("Terminal-head formula mismatch");
  if (eventCount !== expectedEvents) throw new Error("11110000 event-count formula mismatch");
  if (halt.steps !== expectedHalt) throw new Error("Terminal-to-halt cost mismatch");

  return {
    L,
    terminalL: terminal.L,
    terminalA: terminal.a,
    terminalHead: terminal.head,
    movesToTerminal: terminal.steps,
    q4_11110000_events: eventCount,
    firstEvents,
    lastEvents,
    terminalMoves: terminalCost,
    haltMoves: halt.steps,
  };
}

const limits = new Map([[2, 100000], [4, 2000000], [6, 20000000]]);
const results = [2, 4, 6].map(L => runCase(L, limits.get(L)));
process.stdout.write(JSON.stringify(results, null, 2) + "\n");
