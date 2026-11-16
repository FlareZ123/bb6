#!/usr/bin/env node
// Finite diagnostic replay of the pinned BB6 high-level section recurrence.
// This is a source transcription, not a proof. Compare any decisive checkpoint
// against Agent49ParitySource.run in Lean before relying on it.

function evalA(a, k, m) {
  while (true) {
    if (k % 3n === 2n) return [a + 1n, k / 3n, m];
    if (a === 0n) return k % 3n === 0n ? null : [0n, k / 3n, m];
    if (k % 3n === 0n) return [a - 1n, k / 3n, m + 2n];
    k = k / 3n;
    m += 2n * k + 3n;
    a -= 1n;
  }
}

function drainB(a, b, d) {
  while (b !== 0n) {
    const next = evalA(a, b - 1n, d + 2n * b + 3n);
    if (next === null || next[1] >= b) return null;
    [a, b, d] = next;
  }
  return [a, d];
}

function highLevelNext(a, d) {
  if (a === 0n)
    return d % 2n === 1n ? drainB(d + 1n, 2n, 2n) : [d, 7n];
  if (d % 2n === 1n && a >= d + 5n)
    return drainB(a - d - 5n, d + 3n, 5n);
  if (d % 2n === 0n && a >= d + 3n)
    return drainB(a - d - 2n, d + 2n, 2n);
  if (a % 2n === 1n) return null;
  if (a === d + 2n) return drainB(0n, a, 2n);
  if (d % 2n === 1n) return drainB(d + 4n - a, a - 1n, 3n);
  const p = evalA(d + 1n - a, a, 2n * a + 5n);
  return p === null ? null : drainB(...p);
}

function ceilDiv(a, b) {
  return (a + b - 1n) / b;
}

function abs(n) {
  return n < 0n ? -n : n;
}

const maxStep = Number(process.argv[2] || 100);
const firstScale = Number(process.argv[3] || 10);
const lastScale = Number(process.argv[4] || 20);

const states = [{ n: 0, a: 0n, d: 7n, mass: 7n }];
let a = 0n, d = 7n;
for (let n = 1; n <= maxStep; n++) {
  const p = highLevelNext(a, d);
  if (p === null) break;
  [a, d] = p;
  states.push({ n, a, d, mass: a + d });
}

const rows = [];
for (let scale = firstScale; scale <= lastScale; scale++) {
  const mLo = 3n ** BigInt(scale - 1) - 3n;
  const mHi = 3n ** BigInt(scale) - 4n;
  const E = 35n * BigInt(scale) + 120n;
  const nearLo = ceilDiv(11n * mLo - E, 4n);
  const nearHi = (11n * mHi + E) / 4n;
  const farLo = 14n * mLo - E;
  const farHi = 14n * mHi + E;

  const near = states.filter(s => nearLo <= s.mass && s.mass <= nearHi).map(s => {
    const m = s.a < s.d ? s.a : s.d;
    const L = s.a < s.d ? s.d : s.a;
    return { n: s.n, mass: s.mass, residual: abs(4n * L - 7n * m) };
  });
  const far = states.filter(s => farLo <= s.mass && s.mass <= farHi).map(s => {
    const m = s.a < s.d ? s.a : s.d;
    const L = s.a < s.d ? s.d : s.a;
    return { n: s.n, mass: s.mass, residual: abs(L - 13n * m) };
  });

  const minResidual = xs => xs.length
    ? xs.reduce((v, x) => x.residual < v ? x.residual : v, xs[0].residual)
    : null;
  rows.push({
    scale,
    E,
    mLo,
    mHi,
    nearMass: [nearLo, nearHi],
    nearIndices: near.map(x => x.n),
    nearMinResidual: minResidual(near),
    farMass: [farLo, farHi],
    farIndices: far.map(x => x.n),
    farMinResidual: minResidual(far)
  });
}

const json = {
  maxStepReached: states[states.length - 1].n,
  checkpoint39to46: states.filter(s => s.n >= 33 && s.n <= 46),
  corridorRows: rows
};
console.log(JSON.stringify(json, (_, v) => typeof v === "bigint" ? v.toString() : v, 2));
