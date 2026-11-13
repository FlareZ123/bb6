#!/usr/bin/env node
"use strict";

// Reproduce the first 12 Hensel residues for
// F(r)=463*2^(885+13122r)-8517418*(887+13122r)-12409413.
// This is an exact BigInt modular computation; it does not replace the
// LTE proof of the 3-adic isometry in Feeder887Hensel.md.

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

const mod3pow9 = 3n ** 9n;
const mod3pow10 = 3n ** 10n;
assert(Fmod(0n, 1) === 13122n, "F(0) mod 3^9 mismatch");
assert(powMod(2n, 13122n, mod3pow10) === 19684n,
  "2^13122 mod 3^10 mismatch");

let root = 0n;
const rows = [];
for (let k = 1; k <= 12; k++) {
  const step = 3n ** BigInt(k - 1);
  const candidates = [root, root + step, root + 2n * step];
  const hits = candidates.filter(r => Fmod(r, k) === 0n);
  assert(hits.length === 1, `precision ${k}: expected one Hensel lift`);
  const next = hits[0];
  rows.push({
    precision: k,
    modulus: (3n ** BigInt(k)).toString(),
    residue: next.toString(),
    digit: ((next - root) / step).toString()
  });
  root = next;
}

const expected = ["1", "4", "13", "13", "13", "499",
  "1228", "1228", "14350", "14350", "132448", "486742"];
assert(rows.every((x, i) => x.residue === expected[i]),
  "Hensel residue sequence changed");

console.log(JSON.stringify(rows, null, 2));
