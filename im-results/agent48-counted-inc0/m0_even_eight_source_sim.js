#!/usr/bin/env node
"use strict";

// Independent finite simulator for the original TM63 table in
// im-results/agent48-champion-root/ChampionRootBridge.lean.
// Exhaustively checks the generic M0, n=8q source increment over a bounded
// parameter box. This is computational evidence only, not a Lean proof.

const d0 = [false, false, true];
const d1 = [true, true, true];
const lh = [true, true, false, true, true, true];

function marker(m) {
  if (m % 3 === 0) return [false, true];
  if (m % 3 === 1) return [true, false, true];
  return [true, true, false, true];
}
function d1pow(n) {
  return Array.from({ length: 3 * n }, () => true);
}
function binDec(len, n) {
  let p = 2 ** (len + 1) - 1 - n;
  const out = [];
  for (let i = 0; i < len; i++) {
    if (p <= 1) break;
    if (p % 2 === 0) {
      out.push(...d0);
      p = Math.floor(p / 2);
    } else {
      out.push(...d1);
      p = Math.floor(p / 2);
    }
  }
  return out;
}
function s1LeftFacing(L, n, m, a, z) {
  return [...binDec(a, z), ...marker(m), ...d0, ...binDec(L, n), ...lh];
}
function s0RightFacing(b) {
  return [false, true, true, true, false, false, ...d1pow(b + 1)];
}
function q4LeftFacing(L, q, a) {
  return [
    true,
    ...d1pow(a - 1),
    ...marker(2),
    ...d0, ...d0, ...d0, ...d0,
    ...d1,
    ...binDec(L - 4, Math.floor(q / 2)),
    ...lh,
  ];
}
function q4RightFacing(b) {
  return [true, true, true, true, false, false, ...d1pow(b + 1)];
}

// Each transition is [write, moveRight, nextState]. null is the halting
// transition (state 0 reading 1).
const tm2 = new Map([
  ['0,0', [true,  true,  1]],
  ['1,0', [true,  false, 2]],
  ['1,1', [false, true,  5]],
  ['2,0', [true,  true,  4]],
  ['2,1', [false, false, 3]],
  ['3,0', [false, false, 2]],
  ['3,1', [true,  true,  1]],
  ['4,0', [true,  true,  0]],
  ['4,1', [true,  true,  4]],
  ['5,0', [true,  true,  4]],
  ['5,1', [false, true,  3]],
]);

function initialConfig(L, n, m, a, z, b, head = 0) {
  const left = s1LeftFacing(L, n, m, a, z);
  const right = s0RightFacing(b);
  const tape = new Map();
  left.forEach((bit, i) => { if (bit) tape.set(head - i, true); });
  right.forEach((bit, i) => { if (bit) tape.set(head + 1 + i, true); });
  return { tape, state: 3, head };
}
function step(config) {
  const bit = config.tape.get(config.head) === true ? 1 : 0;
  const transition = tm2.get(String(config.state) + ',' + String(bit));
  if (!transition) return false;
  const [write, moveRight, nextState] = transition;
  if (write) config.tape.set(config.head, true);
  else config.tape.delete(config.head);
  config.state = nextState;
  config.head += moveRight ? 1 : -1;
  return true;
}
function advance(config, steps) {
  for (let i = 0; i < steps; i++) {
    if (!step(config)) {
      return { ok: false, haltedAt: i, state: config.state, head: config.head };
    }
  }
  return { ok: true };
}
function matches(config, state, head, left, right) {
  if (config.state !== state || config.head !== head) return false;
  const expectedOnes = new Set();
  left.forEach((bit, i) => { if (bit) expectedOnes.add(head - i); });
  right.forEach((bit, i) => { if (bit) expectedOnes.add(head + 1 + i); });
  if (expectedOnes.size !== config.tape.size) return false;
  for (const position of expectedOnes) {
    if (!config.tape.has(position)) return false;
  }
  for (const position of config.tape.keys()) {
    if (!expectedOnes.has(position)) return false;
  }
  return true;
}
function drainCost(b) {
  return 6 * 4 ** b + 42 * 2 ** b - 12 * b - 48;
}
function totalCost(a, b) {
  return 6 * 4 ** b + 42 * 2 ** b + 12 * a - 9 * b + 51;
}
function checkCase(L, q, a, b) {
  const config = initialConfig(L, 8 * q, 0, a, 0, b);
  const prefixSteps = 60 + 12 * a;
  const prefix = advance(config, prefixSteps);
  if (!prefix.ok) return { ok: false, stage: 'q4-prefix-halted', ...prefix };
  if (!matches(config, 4, 0, q4LeftFacing(L, q, a), q4RightFacing(b))) {
    return { ok: false, stage: 'q4-prefix-interface' };
  }

  const suffixSteps = 39 + 3 * b;
  const suffix = advance(config, suffixSteps);
  if (!suffix.ok) return { ok: false, stage: 'q4-suffix-halted', ...suffix };
  const middleHead = 5 + 3 * b;
  if (!matches(config, 3, middleHead,
      s1LeftFacing(L, 8 * q - 1, 2, a + b + 1, 2 ** b - 1),
      s0RightFacing(0))) {
    return { ok: false, stage: 'q4-suffix-interface' };
  }

  const drainSteps = drainCost(b);
  const drain = advance(config, drainSteps);
  if (!drain.ok) return { ok: false, stage: 'counted-drain-halted', ...drain };
  if (!matches(config, 3, middleHead,
      s1LeftFacing(L, 8 * q - 1, 2, a + b + 1, 0),
      s0RightFacing(2 ** b - 1))) {
    return { ok: false, stage: 'counted-drain-interface' };
  }

  const observedSteps = prefixSteps + suffixSteps + drainSteps;
  return {
    ok: observedSteps === totalCost(a, b),
    observedSteps,
    expectedSteps: totalCost(a, b),
  };
}

let tested = 0;
const failures = [];
for (let L = 4; L <= 9; L++) {
  for (let q = 1; q < 2 ** (L - 3); q += 2) {
    for (let a = 1; a <= 6; a++) {
      for (let b = 0; b <= 4; b++) {
        tested++;
        const result = checkCase(L, q, a, b);
        if (!result.ok) failures.push({ L, q, a, b, ...result });
      }
    }
  }
}
if (failures.length !== 0) {
  console.error(JSON.stringify({ tested, failures: failures.slice(0, 10) }, null, 2));
  process.exit(1);
}
console.log('PASS: ' + tested + ' exhaustive bounded cases; no prefix, suffix, drain, or cost mismatches.');
console.log('Domain: 4<=L<=9, odd 1<=q<2^(L-3), 1<=a<=6, 0<=b<=4.');
console.log('This is computational evidence, not a formal proof or a BB(6) upper bound.');
