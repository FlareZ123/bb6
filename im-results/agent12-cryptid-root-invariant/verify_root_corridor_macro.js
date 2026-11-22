#!/usr/bin/env node
"use strict";

// Source-correct regression checks for the DR right-head-one root cycle.
// The former corridor, countdown, and 76-step endpoints are asserted to fail.
// This is an executable transcription of source clauses, not a Lean proof.

const bump = xs => xs.length ? [xs[0] + 1, ...xs.slice(1)] : [1];
const bumpN = (xs, n) => {
  let out = xs.slice();
  for (let i = 0; i < n; i++) out = bump(out);
  return out;
};
const zeros = n => Array(n).fill(0);
const repeat = (xs, n) => Array(n).fill(xs).flat();
const eq = (a, b) => JSON.stringify(a) === JSON.stringify(b);
const state = (mode, L, R) => ({ mode, L, R });

function bounceCR(r, k, a, x) {
  let right = x.slice();
  while (right.length) {
    const v = right[0], t = right.slice(1);
    if (v === 0) { k += 2; right = t; continue; }
    if (v === 1) {
      if (!t.length) return { a: [k + 1, ...a], right: [0, 0, 1] };
      const w = t[0], u = t.slice(1);
      if (w === 0) { a = [k + 4, ...a]; k = 0; right = u; continue; }
      if (w === 1) {
        if (!u.length) return { a: [k + 1, ...a], right: [0, 1] };
        return { a: [k + 1, ...a], right: [0, u[0] + 2, ...u.slice(1)] };
      }
      return bounceDR(r, [1, k + 1, ...a], [w - 2, ...u]);
    }
    return { halt: "tok_CR add2" };
  }
  if (k === 0) return { a, right: [1] };
  if (k === 1) return { a: [0, ...a], right: [0, 1] };
  if (k === 2) return { a: [1, ...a], right: [0, 1] };
  return { a: [k - 1, ...a], right: [0, 1] };
}

function bounceDR(r, a, x) {
  let right = x.slice();
  while (right.length) {
    const v = right[0], t = right.slice(1);
    if (v === 0) { a = [1, ...a]; right = t; continue; }
    if (v === 1 && !t.length) return { a: [1, ...a], right: [0, 0, 1] };
    return bounceCR(r, 0, [1, ...a], [v - 1, ...t]);
  }
  return { a, right: [1] };
}

function normalizeEL(k, r, x) {
  let kk = k.slice(), right = x.slice();
  while (kk.length) {
    const v = kk[0], t = kk.slice(1);
    if (v === 0) {
      if (!t.length) return state("CR", [0, ...right], bump(r));
      const z = bounceCR(r, t[0] + 2, t.slice(1), right);
      if (z.halt) return z;
      kk = z.a; right = z.right; continue;
    }
    if (v === 1) { kk = t; right = [0, ...right]; continue; }
    if (v === 2) { kk = t; right = [1, 0, ...right]; continue; }
    // tok_EL_add3 preserves (0 :: right); tok_DR_zero consumes that zero
    // before bounce_DR, so the bounce starts on the suffix 'right'.
    const z = bounceDR(r, [1, v - 3, ...t], right);
    if (z.halt) return z;
    kk = z.a; right = z.right;
  }
  return state("EL", [0, ...right], r.slice());
}

let tokenCalls = 0;
function closeTokDR(r, x) {
  tokenCalls++;
  const z = bounceDR(r, [0], x);
  return z.halt ? z : normalizeEL(z.a, r, z.right);
}
function closeTokCR(r, x) {
  tokenCalls++;
  const z = bounceCR(r, 0, [0], x);
  return z.halt ? z : normalizeEL(z.a, r, z.right);
}

function step(s) {
  const { mode, L, R } = s;
  if (mode === "CR") {
    if (!L.length) return state("EL", [0], bump(R));
    const a = L[0], t = L.slice(1);
    if (a === 0) return state("CR", t, bumpN(R, 2));
    if (a === 1) {
      if (!t.length) return state("EL", [0], [0, ...bumpN(R, 3)]);
      const b = t[0], u = t.slice(1);
      if (b === 0) return state("CR", [1, ...u], [0, 0, ...bump(R)]);
      if (b === 1) {
        if (!u.length) return state("EL", [0, 0, 0, 0], [1, 0, ...R]);
        return state("EL", [0, 0, 0, 0, ...u], [0, 0, ...bump(R)]);
      }
      return state("DR", [0, ...u], [1, b - 2, ...R]);
    }
    return { halt: "CR head >= 2" };
  }
  if (mode === "EL") {
    if (!R.length) return state("CR", L, [0]);
    const a = R[0], t = R.slice(1);
    if (a === 0) return state("EL", [0, ...L], t);
    return state("DL", L, [a - 1, ...t]);
  }
  if (mode === "DL") {
    if (!R.length) return state("CR", L, [2]);
    const a = R[0], t = R.slice(1);
    if (a === 0) return state("EL", [0, ...bump(L)], t);
    if (a === 1) return closeTokDR(t, L);
    return state("DR", L, [1, a - 2, ...t]);
  }
  if (mode === "DR") {
    if (!L.length) return state("EL", [0], R);
    const a = L[0], t = L.slice(1);
    if (!R.length) {
      if (a === 0) return state("EL", bump(t), [0]);
      return state("DR", [a - 1, ...t], [0]);
    }
    const b = R[0], u = R.slice(1);
    // Source mode_DR tokenizes only r1=0. Positive r1 is ordinary;
    // mode_DL has the separate 0/1/>=2 split.
    if (b === 0) return a === 0 ? closeTokDR(u, t) : closeTokCR(u, [a - 1, ...t]);
    if (a === 0) return state("DR", t, [1, b - 1, ...u]);
    return state("CR", [a - 1, ...t], [0, b - 1, ...u]);
  }
  return { halt: "unknown mode" };
}

function run(s, n) {
  for (let i = 0; i < n; i++) {
    s = step(s);
    if (s.halt) throw new Error("halt at offset " + (i + 1) + ": " + s.halt);
  }
  return s;
}
const Corr = (r, c) => state("DR", [...zeros(r), 1], [1, c]);
const F = r => state("EL", zeros(4), [1, 0, 0, 0, ...repeat([1, 0], r + 2), 3]);
const G = r => state("DR", [0, 0, ...repeat([1, 0], r + 2), 0, 0, 1, 0, 0, 0], [1, 0]);
const H = r => state("CR", [0, ...repeat([1, 0], r + 1), 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0]);

function assertState(label, actual, expected) {
  if (!eq(actual, expected)) {
    throw new Error(label + "\nactual=" + JSON.stringify(actual) + "\nexpected=" + JSON.stringify(expected));
  }
}

let checks = 0;
const root = state("DR", [0, 0], [1]);

// In mode_DR, r1=1 is positive and takes the ordinary execute-4 branch.
assertState("blank-root first source successor", step(root),
  state("DR", [0], [1, 0])); checks++;
assertState("blank-root second source successor", run(root, 2),
  state("DR", [], [1, 0, 0])); checks++;
assertState("blank-root third source successor", run(root, 3),
  state("EL", [0], [1, 0, 0])); checks++;
assertState("blank-root 24-successor corridor entry", run(root, 24),
  Corr(3, 3)); checks++;

// Exact source token-closure formula on the zero-run inputs used by the root.
for (let n = 0; n <= 32; n++) {
  assertState("closeTokDR 0^" + n, closeTokDR([], zeros(n)),
    state("CR", [...zeros(n + 1), 1], [1])); checks++;
}

// The proposed 36-step cycle misread the final DR right-head-one case.
// The correct source branch is ordinary and returns to DR.
for (const c of [1, 2, 3, 7, 1000, 714286]) {
  assertState("CR candidate final edge c=" + c,
    run(state("CR", [0, 0, 1], [c]), 7),
    state("DR", [0], [1, 0, c + 4])); checks++;
}

// Parameterized countdown macro samples and the finite reset.
const D = (n, c) => state("CR", [0], [...zeros(4 * n + 5), c]);
let countdownChecks = 0;
for (let n = 0; n <= 6; n++) {
  for (const c of [3, 4, 5, 10, 540]) {
    assertState("D_n countdown n=" + n + " c=" + c,
      run(D(n, c), 8 * n + 24), D(n + 1, c - 3));
    countdownChecks++; checks++;
  }
}
assertState("D_180(0) 1481-successor reset", run(D(180, 0), 1481),
  D(0, 1453)); checks++;

// Root-reachable DR/G/B block insertion: test distinct arbitrary finite tails.
const G0 = [0, 0, 1, 0, 1, 0, 0, 0, 0, 1];
const B0 = [16, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0];
const suffixes = [[], [0], [1], [3, 0, 0], [7, 5, 3, 1],
  [12, 0, 0, 0, 12, 0, 0, 0, 2]];
let growthChecks = 0;
for (const suffix of suffixes) {
  const before = tokenCalls;
  assertState("DR/G/B 76-step insertion suffix=" + JSON.stringify(suffix),
    run(state("DR", G0, [1, ...B0, ...suffix]), 76),
    state("DR", G0, [1, ...B0, ...B0, ...suffix]));
  if (tokenCalls !== before) throw new Error("DR/G/B macro unexpectedly called a token normalizer");
  growthChecks++; checks++;
}

// The separate H-phase CR macro also survives the source-correct DR rule.
const P = [0, 0, 1, 0, 19];
const HB = [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 16];
const U = [0, 0, 0, 12, 0, 0, 0, 12, 0, 0, 0, 12, 0, 0, 0, 2, 0, 0, 0, 0];
const tokenBeforeH = tokenCalls;
assertState("H-phase CR 76-step insertion",
  run(state("CR", [1, 0], [...P, ...HB, ...U]), 76),
  state("CR", [1, 0], [...P, ...HB, ...HB, ...U]));
if (tokenCalls !== tokenBeforeH) throw new Error("H-phase macro unexpectedly called a token normalizer");
checks++;

console.log(JSON.stringify({
  ok: true, checks, countdownChecks, growthChecks,
  rootPrefix24: run(root, 24),
  d180Reset: run(D(180, 0), 1481),
  hPhase76: run(state("CR", [1, 0], [...P, ...HB, ...U]), 76),
}, null, 2));
