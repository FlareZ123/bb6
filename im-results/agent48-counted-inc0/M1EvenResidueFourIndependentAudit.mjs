#!/usr/bin/env node
/**
 * Independent JavaScript replay for Agent 41's m=1, n=8k+4 candidate.
 *
 * This is finite computational corroboration only.  The transition table is
 * transcribed from Agent48Champion.tm2 in ChampionRootBridge.lean and the S1
 * encoding is transcribed from the corresponding source definitions.  It is
 * not a proof of the quantified Lean theorem or of an infinite-tape invariant.
 *
 * Run from the repository root:
 *   node im-results/agent48-counted-inc0/M1EvenResidueFourIndependentAudit.mjs
 */
import assert from "node:assert/strict";

// Each transition is [writeBit, displacement, nextState]; null means halt.
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
  switch (m % 3) {
    case 0: return [false, true];
    case 1: return [true, false, true];
    default: return [true, true, false, true];
  }
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
  const read = config.ones.has(config.head);
  const transition = TM2[config.state][read ? 1 : 0];
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

function checkFiniteBridge() {
  const input = [-10, -9, -8, -7, -6, -5, -4, -1, 2, 3, 4, 5];
  const output = [-12, -11, -10, -7, -4, -1, 1, 2, 3, 4, 5];
  const replay = runWithHeads(
    { state: 3, head: 0, ones: new Set(input) }, 53,
  );
  assertSameConfig(
    replay.config,
    { state: 4, head: 5, ones: new Set(output) },
    "53-step bridge",
  );
  assert.ok(replay.heads.every(h => -12 <= h && h <= 5));
}

function checkCase(L, k, a, b) {
  const n = 8 * k + 4;
  const initial = s1Config(L, n, 1, a, 0, b, 0);
  const swept = runWithHeads(initial, 9 * a + 3).config;
  assert.ok(swept !== null);
  assert.equal(swept.state, 3);
  assert.equal(swept.head, -(3 * a + 1));

  const bridgeInput = new Set([-10, -9, -8, -7, -6, -5, -4, -1, 2, 3, 4, 5]);
  for (let rel = -12; rel <= 5; rel++) {
    assert.equal(
      swept.ones.has(swept.head + rel),
      bridgeInput.has(rel),
      `bridge input L=${L}, k=${k}, a=${a}, b=${b}, rel=${rel}`,
    );
  }

  const bridge = runWithHeads(swept, 53);
  assert.ok(bridge.config !== null);
  assert.equal(bridge.config.state, 4);
  assert.equal(bridge.config.head, swept.head + 5);
  assert.ok(bridge.heads.every(
    h => -12 <= h - swept.head && h - swept.head <= 5,
  ));
  const bridgeOutput = new Set([-12, -11, -10, -7, -4, -1, 1, 2, 3, 4, 5]);
  for (let rel = -12; rel <= 5; rel++) {
    assert.equal(
      bridge.config.ones.has(swept.head + rel),
      bridgeOutput.has(rel),
      `bridge output L=${L}, k=${k}, a=${a}, b=${b}, rel=${rel}`,
    );
  }

  // The q4 prefix consists of the sweep, 53-step bridge, and 3*a E-scan.
  const prefix = runWithHeads(initial, 56 + 12 * a).config;
  assert.ok(prefix !== null);
  assert.equal(prefix.state, 4);
  assert.equal(prefix.head, 4);

  const q4Left = [
    true, ...Array(3 * a).fill(true), ...markerWord(0),
    ...D0, ...D0, ...D0, ...D1, ...binDec(L - 3, k), ...LH,
  ];
  for (let i = 0; i < q4Left.length; i++) {
    assert.equal(
      prefix.ones.has(-i),
      q4Left[i],
      `q4 left word L=${L}, k=${k}, a=${a}, b=${b}, i=${i}`,
    );
  }

  // q4RightShape is expressed relative to the original head h=0.
  for (let i = 0; i < 5; i++) assert.ok(prefix.ones.has(i));
  assert.ok(!prefix.ones.has(5));
  assert.ok(!prefix.ones.has(6));
  for (let i = 0; i < 3 * (b + 1); i++) {
    assert.ok(prefix.ones.has(7 + i));
  }
  for (let i = 0; i < 5; i++) {
    assert.ok(!prefix.ones.has(10 + 3 * b + i));
  }

  // Full reset prefix only; the all-ones counted drain is a separate theorem.
  const actual = runWithHeads(initial, 91 + 12 * a + 3 * b).config;
  const expected = s1Config(
    L, n - 1, 0, a + b + 2, 2 ** b - 1, 0, 5 + 3 * b,
  );
  assertSameConfig(actual, expected, `reset prefix L=${L}, k=${k}, a=${a}, b=${b}`);
}

function main() {
  checkFiniteBridge();
  let cases = 0;
  for (let L = 3; L <= 8; L++) {
    for (let k = 0; 8 * k + 4 < 2 ** L; k++) {
      for (let a = 0; a <= 3; a++) {
        for (let b = 0; b <= 2; b++) {
          checkCase(L, k, a, b);
          cases++;
        }
      }
    }
  }
  assert.equal(cases, 756);
  console.log("53-step bridge: exact endpoint and head confinement [-12,5]");
  console.log(`m=1 residue-four reset-prefix replay: ${cases} cases passed`);
  console.log("Scope: finite replay only; not a Lean theorem or axiom audit.");
}

main();
