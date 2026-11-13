#!/usr/bin/env node
"use strict";

// Reproduce the first Hensel residues and band-compatible exponents for
// F(r)=463*2^(885+13122r)-8517418*(887+13122r)-12409413.
// Exact BigInt modular arithmetic; the LTE and irrational-rotation proofs
// are in Feeder887Hensel.md.

function mod(a, m) {
  const r = a % m;
  return r < 0n ? r + m : r;
}

function powMod(a, e, m) {
  let x = mod(a, m);
  let y = 1n;
  while (e > 0n) {
    if ((e & 1n) !== 0n) y = y * x % m;
    x = x * x % m;
    e >>= 1n;
  }
  return y;
}

function Fmod(r, k) {
  const m = 3n ** BigInt(k + 8);
  const A = powMod(2n, 13122n, m);
  const B = powMod(2n, 885n, m);
  const n = 887n + 13122n * r;
  return mod(463n * B * powMod(A, r, m)
    - 8517418n * n - 12409413n, m);
}

function assert(condition, message) {
  if (!condition) throw new Error(message);
}

assert(Fmod(0n, 1) === 13122n, "F(0) mod 3^9 mismatch");
assert(powMod(2n, 13122n, 3n ** 10n) === 19684n,
  "2^13122 mod 3^10 mismatch");

let root = 0n;
const roots = [];
for (let k = 1; k <= 12; k++) {
  const step = 3n ** BigInt(k - 1);
  const candidates = [root, root + step, root + 2n * step];
  const hits = candidates.filter(r => Fmod(r, k) === 0n);
  assert(hits.length === 1, `precision ${k}: expected one Hensel lift`);
  const next = hits[0];
  roots.push({
    precision: k,
    modulus: (3n ** BigInt(k)).toString(),
    residue: next.toString(),
    digit: ((next - root) / step).toString()
  });
  root = next;
}

const expectedRoots = ["1", "4", "13", "13", "13", "499",
  "1228", "1228", "14350", "14350", "132448", "486742"];
assert(roots.every((x, i) => x.residue === expectedRoots[i]),
  "Hensel residue sequence changed");

const bandCompatible = [];
for (let t = 1; t <= 60; t++) {
  const scale = 3n ** BigInt(t - 1);
  const left = 6n * 6561n * scale;
  const right = 8n * 6561n * scale;
  for (let j = 0; j <= 2 * t + 20; j++) {
    const numerator = 463n * 2n ** BigInt(t + j);
    if (left < numerator && numerator < right) {
      let evenChain = 0;
      for (let m = 1; m <= 30; m++) {
        const two = 2n ** BigInt(m - 1);
        if (numerator * two > scale * 6561n * (8n * two - 1n))
          evenChain = m;
        else
          break;
      }
      bandCompatible.push({ t, j, evenChain });
      break;
    }
  }
}
const expectedBand = [[2,6,0],[5,8,1],[7,9,0],[10,11,2],
  [12,12,0],[15,14,4],[17,15,1],[19,16,0],
  [22,18,1],[24,19,0],[27,21,3],[29,22,0]];
assert(expectedBand.every(([t,j,m], i) =>
  bandCompatible[i]?.t === t &&
  bandCompatible[i]?.j === j &&
  bandCompatible[i]?.evenChain === m),
  "band-compatible exponent/chain sequence changed");

console.log(JSON.stringify({ roots, bandCompatible }, null, 2));
