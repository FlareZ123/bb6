#!/usr/bin/env node
"use strict";

// Array-based regression checks for RootCorridorMacro.md.
// This is an executable transcription of the outer stack/token clauses,
// not a proof. The Lean/source derivations are described in the Markdown note.

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

function closeTokDR(r, x) {
  const z = bounceDR(r, [0], x);
  return z.halt ? z : normalizeEL(z.a, r, z.right);
}
function closeTokCR(r, x) {
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
for (let r = 1; r <= 8; r++) {
  assertState("c=3, r=" + r, run(Corr(r, 3), 2 * r + 14), Corr(r + 4, 0)); checks++;
  assertState("c=6, r=" + r, run(Corr(r, 6), 2 * r + 14), Corr(r + 4, 3)); checks++;
  assertState("c=0, r=" + r, run(Corr(r, 0), 3 * r + 32), Corr(3, 2 * r + 7)); checks++;
  if (r >= 8) {
    assertState("c=2 corrected sweep, r=" + r,
      run(Corr(r, 2), 2 * r + 30),
      state("CR", [...zeros(r - 8), 1], [33])); checks++;
  }
  assertState("c=1, r=" + r, run(Corr(r, 1), 3 * r + 20), F(r)); checks++;
  assertState("F-to-G, r=" + r, run(F(r), 3 * r + 13), G(r)); checks++;
  assertState("G-to-H, r=" + r, run(G(r), 4), H(r)); checks++;
}

// Arbitrary-tail transfer identity, with nonempty U and T.
for (let r = 1; r <= 8; r++) {
  const U = [0, 2], T = [3, 0, 1];
  const start = state("DR", [...zeros(r), 1, ...U], [1, ...T]);
  const expected = state("CR", [0, ...U], [...zeros(r + 2), ...T]);
  assertState("arbitrary-tail transfer, r=" + r, run(start, r + 1), expected);
  checks++;
}

// Exact #85 token-closure outputs. Each tok_EL_1 consumes one leading 1
// in K and prepends one zero to the right word.
for (let n = 0; n <= 32; n++) {
  assertState("closeTokDR 0^" + n, closeTokDR([], zeros(n)),
    state("CR", [...zeros(n + 1), 1], [1]));
  checks++;
  assertState("closeTokDR 0^" + n + "1", closeTokDR([], [...zeros(n), 1]),
    state("CR", [...zeros(n + 4), 1], [1]));
  checks++;
}
assertState("closeTokCR [1,1]", closeTokCR([], [1, 1]),
  state("CR", [0, 0, 0, 1], [1])); checks++;
assertState("closeTokCR [1,1,2,5]", closeTokCR([], [1, 1, 2, 5]),
  state("CR", [0, 0, 0, 4, 5], [1])); checks++;

assertState("root stack seed to Corr(3,3)", run(state("DR", [0, 0], [1]), 24), Corr(3, 3)); checks++;

const rootChain = [
  [Corr(3, 3), 20, Corr(7, 0)],
  [Corr(7, 0), 53, Corr(3, 21)],
  [Corr(3, 21), 20, Corr(7, 18)],
  [Corr(31, 0), 125, Corr(3, 69)],
  [Corr(95, 0), 317, Corr(3, 197)],
  [Corr(263, 2), 556, state("CR", [...zeros(255), 1], [33])],
  [state("CR", [...zeros(255), 1], [33]), 256, state("EL", [0], [0, 546])]
];
for (let i = 0; i < rootChain.length; i++) {
  const [start, n, expected] = rootChain[i];
  assertState("root chain " + i, run(start, n), expected);
  checks++;
}

console.log(JSON.stringify({ ok: true, checks }, null, 2));
