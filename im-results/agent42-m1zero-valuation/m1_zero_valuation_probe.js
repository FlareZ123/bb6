#!/usr/bin/env node
"use strict";

// Exact finite-support replay of the original TM63 table and S1 encoder.
// This is computational evidence only; it is not a Lean proof.

const D0 = [false, false, true];
const D1 = [true, true, true];
const LH = [true, true, false, true, true, true];
const RIGHT_BASE = [false, true, true, true, false, false];

const TM2 = [
  [[true, 1, 1], null],
  [[true, -1, 2], [false, 1, 5]],
  [[true, 1, 4], [false, -1, 3]],
  [[false, -1, 2], [true, 1, 1]],
  [[true, 1, 0], [true, 1, 4]],
  [[true, 1, 4], [false, 1, 3]],
];

const M1_ZERO_ODD_BRIDGE_START = [
  -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -1, 2,
];

function markerWord(m) {
  if (m % 3 === 0) return [false, true];
  if (m % 3 === 1) return [true, false, true];
  return [true, true, false, true];
}

function binDec(len, n) {
  let p = (1n << BigInt(len + 1)) - 1n - n;
  const out = [];
  for (let i = 0; i < len; i++) {
    if (p <= 1n) break;
    out.push(...(p % 2n === 0n ? D0 : D1));
    p /= 2n;
  }
  return out;
}

function s1Config(L, n, m, a, z, b, head) {
  const left = [
    ...binDec(a, BigInt(z)),
    ...markerWord(m),
    ...D0,
    ...binDec(L, n),
    ...LH,
  ];
  const right = [
    ...RIGHT_BASE,
    ...Array(b + 1).fill(D1).flat(),
  ];
  const tape = new Map();
  left.forEach((bit, i) => { if (bit) tape.set(head - i, true); });
  right.forEach((bit, i) => { if (bit) tape.set(head + 1 + i, true); });
  return { state: 3, head, tape };
}

function step(c) {
  const bit = c.tape.has(c.head);
  const transition = TM2[c.state][bit ? 1 : 0];
  if (!transition) return false;
  const [write, displacement, nextState] = transition;
  if (write) c.tape.set(c.head, true);
  else c.tape.delete(c.head);
  c.head += displacement;
  c.state = nextState;
  return true;
}

function run(c, steps) {
  for (let i = 0; i < steps; i++) {
    if (!step(c)) return false;
  }
  return true;
}

function sameTape(x, y) {
  if (x.tape.size !== y.tape.size) return false;
  for (const cell of x.tape.keys()) if (!y.tape.has(cell)) return false;
  return true;
}

function v2(n) {
  let t = 0;
  while (n % 2n === 0n) {
    n /= 2n;
    t++;
  }
  return t;
}

// The dynamic bridge is the 62+12t-step extension of the 62-step
// m=1,n=8,k=1 bridge. Preserve FConfig's exact List insertion order.
function finiteBridge(t) {
  let c = {
    state: 3,
    head: 0,
    marks: [
      ...M1_ZERO_ODD_BRIDGE_START,
      ...Array.from({ length: 3 * t }, (_, i) => -14 - i),
    ],
  };
  let minHead = 0;
  let maxHead = 0;
  const total = 62 + 12 * t;
  for (let j = 0; j < total; j++) {
    minHead = Math.min(minHead, c.head);
    maxHead = Math.max(maxHead, c.head);
    const transition = TM2[c.state][c.marks.includes(c.head) ? 1 : 0];
    if (!transition) return { ok: false, failedAt: j };
    const [write, displacement, nextState] = transition;
    c.marks = c.marks.filter(x => x !== c.head);
    if (write) c.marks = [c.head, ...c.marks];
    c.head += displacement;
    c.state = nextState;
  }
  const expected = [
    1, -1, -4, -7, -10, -13,
    ...Array.from({ length: t }, (_, i) => -16 - 3 * i),
    -14 - 3 * t, -15 - 3 * t, 2,
  ];
  return {
    ok: c.state === 4 && c.head === 2 &&
      JSON.stringify(c.marks) === JSON.stringify(expected) &&
      minHead >= -15 - 3 * t && maxHead <= 2,
    minHead,
    maxHead,
    actual: c.marks,
    expected,
  };
}

function main() {
  const bridgeFailures = [];
  for (let t = 0; t <= 100; t++) {
    const result = finiteBridge(t);
    if (!result.ok && bridgeFailures.length < 10) {
      bridgeFailures.push({ t, ...result });
    }
  }

  let sourceCases = 0;
  let sourceFailures = [];
  let maxSteps = 0;
  for (let t = 0; t <= 100; t++) {
    for (const u of [1, 3, 5, 7, 9, 11, 13, 15]) {
      const k = (1n << BigInt(t)) * BigInt(u);
      const n = 8n * k;
      const L = t + Math.ceil(Math.log2(8 * u + 1));
      for (const a of [1, 2, 3]) {
        for (const b of [0, 1, 2]) {
          const c = s1Config(L, n, 1, a, 0, b, 0);
          const prefixSteps = 64 + 12 * a + 12 * t;
          const suffixSteps = 39 + 3 * b;
          maxSteps = Math.max(maxSteps, prefixSteps + suffixSteps);

          const prefixOk =
            run(c, prefixSteps) && c.state === 4 && c.head === 0;
          const suffixOk = prefixOk && run(c, suffixSteps);
          const target = s1Config(
            L, n - 1n, 0, a + b + 2, (1n << BigInt(b)) - 1n, 0, 5 + 3 * b
          );
          const costIdentity =
            prefixSteps + suffixSteps === 103 + 12 * a + 12 * t + 3 * b &&
            103 + 12 * a + 12 * t + 3 * b ===
              48 + 12 * (a + v2(n)) + 15 + 4 + 3 * b;

          const ok = suffixOk && costIdentity &&
            c.state === target.state &&
            c.head === target.head &&
            sameTape(c, target);
          sourceCases++;
          if (!ok && sourceFailures.length < 20) {
            sourceFailures.push({
              t, u, a, b, L, prefixSteps, suffixSteps, prefixOk, suffixOk,
              costIdentity, state: c.state, head: c.head,
              targetState: target.state, targetHead: target.head,
              tapeOnes: c.tape.size, targetOnes: target.tape.size,
            });
          }
        }
      }
    }
  }

  const report = {
    bridgeCases: 101,
    bridgeFailures,
    sourceCases,
    maxSourceSteps: maxSteps,
    sourceFailures,
    status: bridgeFailures.length === 0 && sourceFailures.length === 0
      ? "PASS (bounded computational evidence only)"
      : "FAIL",
  };
  process.stdout.write(JSON.stringify(report, null, 2) + "\n");
  if (report.status.startsWith("FAIL")) process.exitCode = 1;
}

main();
