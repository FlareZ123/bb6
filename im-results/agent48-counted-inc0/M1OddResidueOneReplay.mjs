#!/usr/bin/env node
/**
 * Finite replay for the candidate m=1, n=8*k+1 source row.
 *
 * Transition table and S1 encoding are transcribed from the repository's
 * ChampionRootBridge.lean / S1Encoder.lean conventions.  This script checks
 * finite instances only; it is not a proof of the quantified theorem.
 *
 * Run from repository root:
 *   node im-results/agent48-counted-inc0/M1OddResidueOneReplay.mjs
 */
import assert from "node:assert/strict";

const TM2 = [
  [[true, +1, 1], null],
  [[true, -1, 2], [false, +1, 5]],
  [[true, +1, 4], [false, -1, 3]],
  [[false, -1, 2], [true, +1, 1]],
  [[true, +1, 0], [true, +1, 4]],
  [[true, +1, 4], [false, +1, 3]],
];
const D0 = [false, false, true];
const D1 = [true, true, true];
const LH = [true, true, false, true, true, true];

function markerWord(m) {
  if (m % 3 === 0) return [false, true];
  if (m % 3 === 1) return [true, false, true];
  return [true, true, false, true];
}

function binDec(length, n) {
  assert.ok(Number.isSafeInteger(length) && length >= 0);
  assert.ok(Number.isSafeInteger(n) && n >= 0 && n < 2 ** length);
  let p = 2 ** (length + 1) - 1 - n;
  const out = [];
  for (let i = 0; i < length; i++) {
    if (p <= 1) break;
    out.push(...(p % 2 === 0 ? D0 : D1));
    p = Math.floor(p / 2);
  }
  return out;
}

function s1Config(L, n, m, a, z, b, h = 0) {
  const left = [
    ...binDec(a, z), ...markerWord(m), ...D0, ...binDec(L, n), ...LH,
  ];
  const right = [
    false, true, true, true, false, false,
    ...Array.from({ length: b + 1 }, () => D1).flat(),
  ];
  const ones = new Set();
  left.forEach((bit, i) => { if (bit) ones.add(h - i); });
  right.forEach((bit, i) => { if (bit) ones.add(h + 1 + i); });
  return { state: 3, head: h, ones };
}

function step(config) {
  const transition = TM2[config.state][config.ones.has(config.head) ? 1 : 0];
  if (transition === null) return null;
  const [write, displacement, nextState] = transition;
  const ones = new Set(config.ones);
  if (write) ones.add(config.head);
  else ones.delete(config.head);
  return {
    state: nextState,
    head: config.head + displacement,
    ones,
  };
}

function runWithHeads(initial, count) {
  let config = initial;
  const heads = [config.head];
  for (let i = 0; i < count; i++) {
    config = step(config);
    if (config === null) return { config: null, heads };
    heads.push(config.head);
  }
  return { config, heads };
}

function assertSameConfig(actual, expected, label) {
  assert.ok(actual !== null, label + ": run halted early");
  assert.equal(actual.state, expected.state, label + ": state");
  assert.equal(actual.head, expected.head, label + ": head");
  assert.equal(actual.ones.size, expected.ones.size, label + ": support size");
  for (const x of actual.ones) {
    assert.ok(expected.ones.has(x), label + ": unexpected one at " + x);
  }
}

function checkBridge() {
  const start = [-9, -8, -7, -4, -1, 2, 3, 4];
  const end = [-9, -8, -7, -6, -5, -4, -1, 1, 2, 3, 4];
  const replay = runWithHeads(
    { state: 3, head: 0, ones: new Set(start) }, 29,
  );
  assertSameConfig(
    replay.config,
    { state: 4, head: 5, ones: new Set(end) },
    "29-step residue-one bridge",
  );
  assert.ok(replay.heads.slice(0, -1).every(h => -9 <= h && h <= 4));
}

function checkCase(L, k, a, b) {
  const n = 8 * k + 1;
  const initial = s1Config(L, n, 1, a, 0, b);
  const swept = runWithHeads(initial, 9 * a + 3).config;
  assert.ok(swept !== null);
  assert.equal(swept.state, 3);
  assert.equal(swept.head, -(3 * a + 1));

  const bridgeStart = new Set([-9, -8, -7, -4, -1, 2, 3, 4]);
  for (let rel = -9; rel <= 4; rel++) {
    assert.equal(
      swept.ones.has(swept.head + rel),
      bridgeStart.has(rel),
      `bridge input L=${L}, k=${k}, a=${a}, b=${b}, rel=${rel}`,
    );
  }

  const bridge = runWithHeads(swept, 29);
  assert.ok(bridge.config !== null);
  assert.equal(bridge.config.state, 4);
  assert.equal(bridge.config.head, swept.head + 5);
  assert.ok(bridge.heads.slice(0, -1).every(
    h => -9 <= h - swept.head && h - swept.head <= 4,
  ));
  const bridgeEnd = new Set([-9, -8, -7, -6, -5, -4, -1, 1, 2, 3, 4]);
  for (let rel = -9; rel <= 4; rel++) {
    assert.equal(
      bridge.config.ones.has(swept.head + rel),
      bridgeEnd.has(rel),
      `bridge output L=${L}, k=${k}, a=${a}, b=${b}, rel=${rel}`,
    );
  }

  // Counted left sweep + 29-step bridge + 3*a E-scan.
  const prefix = runWithHeads(initial, 32 + 12 * a).config;
  assert.ok(prefix !== null);
  assert.equal(prefix.state, 4);
  assert.equal(prefix.head, 4);

  const q4Left = [
    true, ...Array(3 * a).fill(true), ...markerWord(0),
    ...D0, ...D1, ...D1, ...D1, ...binDec(L - 3, k), ...LH,
  ];
  for (let i = 0; i < q4Left.length; i++) {
    assert.equal(
      prefix.ones.has(-i),
      q4Left[i],
      `q4 left L=${L}, k=${k}, a=${a}, b=${b}, i=${i}`,
    );
  }

  // The five-cell q4 guard and the active right unary counter.
  for (let i = 0; i < 5; i++) assert.ok(prefix.ones.has(i));
  assert.ok(!prefix.ones.has(5));
  assert.ok(!prefix.ones.has(6));
  for (let i = 0; i < 3 * (b + 1); i++) {
    assert.ok(prefix.ones.has(7 + i));
  }
  for (let i = 0; i < 5; i++) {
    assert.ok(!prefix.ones.has(10 + 3 * b + i));
  }
  for (let i = 9 + 3 * b; i <= 60; i++) {
    assert.ok(!prefix.ones.has(1 + i), `far tail i=${i}`);
  }

  // The q4 cut stream is the exact left-facing target after the 4+35+3b suffix.
  const targetLeft = [
    ...binDec(a + b + 2, 2 ** b - 1),
    ...markerWord(0), ...D0, ...binDec(L, 8 * k), ...LH,
  ];
  const rhs = [
    ...Array(b).fill(D0).flat(),
    ...Array(2).fill(D1).flat(),
    ...q4Left.slice(1),
  ];
  assert.deepEqual(targetLeft, rhs, "q4 suffix target-left identity");

  const target = s1Config(
    L, 8 * k, 0, a + b + 2, 2 ** b - 1, 0, 5 + 3 * b,
  );
  const suffix = runWithHeads(prefix, 35 + 3 * b).config;
  assertSameConfig(suffix, target, "35+3b q4 suffix");
  const full = runWithHeads(initial, 67 + 12 * a + 3 * b).config;
  assertSameConfig(full, target, "complete reset prefix");

  const drain = 6 * 4 ** b + 42 * 2 ** b - 12 * b - 48;
  assert.equal(
    67 + 12 * a + 3 * b + drain + 9 * b,
    6 * 4 ** b + 42 * 2 ** b + 12 * a + 19,
    "counted-cost decomposition",
  );
}

function main() {
  checkBridge();
  let cases = 0;
  for (let L = 3; L <= 8; L++) {
    for (let k = 0; 8 * k + 1 < 2 ** L; k++) {
      for (let a = 0; a <= 3; a++) {
        for (let b = 0; b <= 2; b++) {
          checkCase(L, k, a, b);
          cases++;
        }
      }
    }
  }
  assert.equal(cases, 756);
  console.log("29-step residue-one bridge: exact endpoint and head confinement [-9,4]");
  console.log(`m=1, n=8*k+1 reset-prefix replay: ${cases} cases passed`);
  console.log("Scope: finite replay only; not a Lean theorem or axiom audit.");
}

main();
