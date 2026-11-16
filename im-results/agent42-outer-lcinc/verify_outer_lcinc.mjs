#!/usr/bin/env node
// Reproducible bounded check of the TM63 outer LC_Inc reset-prefix split.
// No dependencies. This is experimental evidence, not a proof.

const TM = [
  [[1, "R", 1], null],          // A: 0 -> 1RB; 1 halts
  [[1, "L", 2], [0, "R", 5]],   // B
  [[1, "R", 4], [0, "L", 3]],   // C
  [[0, "L", 2], [1, "R", 1]],   // D
  [[1, "R", 0], [1, "R", 4]],   // E
  [[1, "R", 4], [0, "R", 3]],   // F
];

const d0 = [0, 0, 1];
const d1 = [1, 1, 1];
const lh = [1, 1, 0, 1, 1, 1];

function binDec(len, value) {
  let p = 2n ** BigInt(len + 1) - 1n - BigInt(value);
  const out = [];
  for (let i = 0; i < len; i++) {
    if (p <= 1n) break;
    out.push(...(p % 2n === 0n ? d0 : d1));
    p /= 2n;
  }
  return out;
}

function markerWord(m) {
  if (m === 0) return [0, 1];
  if (m === 1) return [1, 0, 1];
  return [1, 1, 0, 1];
}

function s1Config(L, n, m, a, z, b) {
  return {
    left: [
      ...binDec(a, z), ...markerWord(m), ...d0,
      ...binDec(L, n), ...lh,
    ],
    right: [0, 1, 1, 1, 0, 0, ...Array(3 * (b + 1)).fill(1)],
  };
}

function v2(n) {
  let r = 0;
  while (n % 2 === 0) {
    n /= 2;
    r++;
  }
  return r;
}

function initialize(config) {
  const tape = new Map();
  config.left.forEach((bit, i) => tape.set(-i, bit));
  config.right.forEach((bit, i) => tape.set(1 + i, bit));
  return { tape, state: 3, head: 0, minHead: 0, maxHead: 0 };
}

function advance(machine, steps) {
  for (let i = 0; i < steps; i++) {
    const transition = TM[machine.state][machine.tape.get(machine.head) || 0];
    if (!transition) throw new Error(`halted at local step ${i}`);
    const [write, direction, nextState] = transition;
    machine.tape.set(machine.head, write);
    machine.head += direction === "R" ? 1 : -1;
    machine.state = nextState;
    machine.minHead = Math.min(machine.minHead, machine.head);
    machine.maxHead = Math.max(machine.maxHead, machine.head);
  }
  return machine;
}

function verifyOne(L, n, m, a, b) {
  const source = s1Config(L, n, m, a, 0, b);
  const machine = initialize(source);
  const r = v2(n);

  // Part 1: source prelude.
  const prelude = 9 * a + 3 * m + 17;
  const h1 = -(3 * a + m + 5);
  advance(machine, prelude);
  if (machine.state !== 3 || machine.head !== h1) {
    throw new Error(`prelude endpoint mismatch: ${[L,n,m,a,b]}`);
  }

  const bit = x => machine.tape.get(x) || 0;
  for (let i = 0; i < 3 * r; i++) {
    if (bit(h1 - i) !== 1) {
      throw new Error(`leftOnes mismatch: ${[L,n,m,a,b]}, i=${i}`);
    }
  }
  if (bit(h1 - 3 * r) !== 0 ||
      bit(h1 - 3 * r - 1) !== 0 ||
      bit(h1 + 1) !== 0) {
    throw new Error(`H-run boundary mismatch: ${[L,n,m,a,b]}`);
  }

  // Part 2: Agent 24's proved H-run interface, checked here by simulation.
  const hRun = 12 * r + 4;
  advance(machine, hRun);
  if (machine.state !== 1 || machine.head !== h1 + 2) {
    throw new Error(`H-run endpoint mismatch: ${[L,n,m,a,b]}`);
  }

  // Part 3: return/transfer postlude.
  const postlude = 3 * a + 42 + m + 3 * b;
  advance(machine, postlude);

  const delta = m === 0 ? 1 : 2;
  const target = s1Config(
    L, n - 1, (m + 2) % 3, a + b + delta, 2n ** BigInt(b) - 1n, 0,
  );
  const targetHead = 3 * b + 5;
  if (machine.state !== 3 || machine.head !== targetHead) {
    throw new Error(`final head/state mismatch: ${[L,n,m,a,b]}`);
  }

  const expected = new Map();
  target.left.forEach((v, i) => expected.set(targetHead - i, v));
  target.right.forEach((v, i) => expected.set(targetHead + 1 + i, v));

  const lo = Math.min(
    machine.minHead, -source.left.length,
    h1 - 3 * r - 5, targetHead - target.left.length,
  ) - 2;
  const hi = Math.max(
    machine.maxHead, source.right.length,
    h1 + 2 + 3 * r + 10, targetHead + target.right.length,
  ) + 2;

  for (let x = lo; x <= hi; x++) {
    if ((machine.tape.get(x) || 0) !== (expected.get(x) || 0)) {
      throw new Error(
        `tape mismatch at x=${x} for ${[L,n,m,a,b]}: ` +
        `${machine.tape.get(x) || 0} != ${expected.get(x) || 0}`,
      );
    }
  }

  return prelude + hRun + postlude;
}

let tested = 0;
let maxSteps = 0;
for (let L = 2; L <= 5; L++) {
  for (let n = 1; n < Math.min(2 ** L, 16); n++) {
    for (let m = 0; m < 3; m++) {
      for (let a = 0; a <= 4; a++) {
        for (let b = 0; b <= 3; b++) {
          const steps = verifyOne(L, n, m, a, b);
          const expected = 12 * a + 63 + 4 * m + 3 * b + 12 * v2(n);
          if (steps !== expected) throw new Error("cost decomposition mismatch");
          tested++;
          maxSteps = Math.max(maxSteps, steps);
        }
      }
    }
  }
}
process.stdout.write(JSON.stringify({
  tested,
  failures: 0,
  maxSteps,
  formula: "12*a + 63 + 4*m + 3*b + 12*v2(n)",
  split: [
    "9*a + 3*m + 17",
    "12*v2(n) + 4",
    "3*a + 42 + m + 3*b",
  ],
}) + "\n");
