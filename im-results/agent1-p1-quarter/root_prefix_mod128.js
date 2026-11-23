#!/usr/bin/env node
"use strict";

// Exact mod-128 over-approximation of the P1 reverse-parent graph.
// Requires only Node.js BigInt support.

const assert = (x, msg) => { if (!x) throw new Error(msg); };
const mod = (x, m) => ((x % m) + m) % m;
const powMod = (a, e, m) => {
  let r = 1n % m, b = a % m;
  while (e > 0n) {
    if (e & 1n) r = r * b % m;
    b = b * b % m;
    e >>= 1n;
  }
  return r;
};
const gcd = (a, b) => { while (b) [a, b] = [b, a % b]; return a; };
const lcm = (a, b) => a / gcd(a, b) * b;

const MOD = 128, MASK = 127, ROOT_ID = 2 * MOD;
const HASH_MASK = (1n << 64n) - 1n;
const families = [
  {
    name: "I", n0: 5362n, delta: 595056n, a: 17n, b: 1058n, c: 636n,
    oddPart: 529n, ordOdd: 253n, expectedP: 128n, expectedU: 1442n,
    base: { D: 36, m: 117, N0: 21 }, shift: { D: 32, m: 32, N0: 32 },
    hashes: { 0: "41fc3ae41d741e03", 3: "9d8525052d0ce383" },
  },
  {
    name: "II", n0: 9538n, delta: 703248n, a: 87n, b: 1198n, c: 712n,
    oddPart: 599n, ordOdd: 299n, expectedP: 5504n, expectedU: 708n,
    base: { D: 124, m: 49, N0: 117 }, shift: { D: 96, m: 96, N0: 96 },
    hashes: { 0: "9d8525052d0ce383", 3: "41fc3ae41d741e03" },
  },
];

function startResidues(f, h) {
  const n = f.n0 + f.delta * BigInt(h);
  const modulus = f.b * 49n * 128n;
  const P = powMod(2n, n, modulus);
  const un = mod(f.a * P - f.c, modulus);
  assert(un % f.b === 0n, "nonintegral u residue");
  const u = un / f.b;
  const dn = mod(18n * P - 196n * u + 14n * n + 48n, 49n * 128n);
  assert(dn % 49n === 0n, "nonintegral D residue");
  return {
    Pmod6272: P % 6272n,
    umod6272: u % 6272n,
    D: Number(dn / 49n),
    m: Number(mod(14n * u - 2n * n - 3n, 128n)),
    N0: Number(mod(14n * P - 2n * n - 7n, 128n)),
  };
}

function verifyPeriod(f) {
  assert(f.b === 2n * f.oddPart, "unexpected denominator factorization");
  assert(f.delta % 7n === 0n, "delta not divisible by 7");
  assert(powMod(2n, f.delta, f.oddPart * 49n) === 1n,
    "period identity modulo odd part failed");
  assert(f.delta === 112n * lcm(f.ordOdd, 21n), "wrong delta/order relation");

  if (f.name === "I") {
    assert(powMod(2n, 253n, 529n) === 1n);
    assert(powMod(2n, 23n, 529n) !== 1n);
    assert(powMod(2n, 11n, 529n) !== 1n);
  } else {
    assert(powMod(2n, 299n, 599n) === 1n);
    assert(powMod(2n, 23n, 599n) !== 1n);
    assert(powMod(2n, 13n, 599n) !== 1n);
  }
  assert(powMod(2n, 21n, 49n) === 1n);
  assert(powMod(2n, 7n, 49n) !== 1n);
  assert(powMod(2n, 3n, 49n) !== 1n);

  const base = startResidues(f, 0);
  assert(base.Pmod6272 === f.expectedP, "wrong base P residue");
  assert(base.umod6272 === f.expectedU, "wrong base u residue");
  assert(base.D === f.base.D && base.m === f.base.m && base.N0 === f.base.N0,
    "wrong base state");

  const dShift = mod(2n * f.delta / 7n, 128n);
  const mShift = mod(-2n * f.delta, 128n);
  assert(Number(dShift) === f.shift.D &&
         Number(mShift) === f.shift.m &&
         Number(mShift) === f.shift.N0, "wrong affine shift");
  assert(4n * dShift % 128n === 0n && 4n * mShift % 128n === 0n,
    "start residues do not repeat modulo four");

  for (let h = 0; h < 4; h++) {
    const s = startResidues(f, h);
    assert(s.D === Number(mod(BigInt(base.D) + BigInt(h) * dShift, 128n)));
    assert(s.m === Number(mod(BigInt(base.m) + BigInt(h) * mShift, 128n)));
    assert(s.N0 === Number(mod(BigInt(base.N0) + BigInt(h) * mShift, 128n)));
  }
}

function closure(start) {
  // k=1..6 are exact; k=7..134 represent all k>=7 modulo 128.
  const costs = [], powers = [];
  for (let k = 1; k < 7; k++) { costs.push(k); powers.push(1 << k); }
  for (let k = 7; k <= 134; k++) { costs.push(k); powers.push(0); }

  const seen = new Uint8Array(MOD * MOD);
  const queue = new Uint16Array(MOD * MOD);
  let head = 0, tail = 0;
  const startId = start.D * MOD + start.m;
  seen[startId] = 1;
  queue[tail++] = startId;

  while (head < tail) {
    const id = queue[head++], D = id >>> 7, m = id & MASK;
    for (let i = 0; i < costs.length; i++) {
      const mp = (m - costs[i]) & MASK;
      const Dp = (powers[i] * D - start.N0 + 2 * mp - 1) & MASK;
      const v = Dp * MOD + mp;
      if (!seen[v]) { seen[v] = 1; queue[tail++] = v; }
    }
  }

  // Independently check that the computed set is successor-closed.
  for (let id = 0; id < seen.length; id++) {
    if (!seen[id]) continue;
    const D = id >>> 7, m = id & MASK;
    for (let i = 0; i < costs.length; i++) {
      const mp = (m - costs[i]) & MASK;
      const Dp = (powers[i] * D - start.N0 + 2 * mp - 1) & MASK;
      assert(seen[Dp * MOD + mp], "closure verification failed");
    }
  }

  let hash = 1469598103934665603n;
  for (const bit of seen) {
    hash ^= BigInt(bit);
    hash = hash * 1099511628211n & HASH_MASK;
  }
  return {
    states: tail,
    rootReachable: seen[ROOT_ID] === 1,
    fnv64: hash.toString(16).padStart(16, "0"),
  };
}

for (const f of families) {
  verifyPeriod(f);
  for (const h of [0, 3]) {
    const s = startResidues(f, h), r = closure(s);
    assert(!r.rootReachable, "root unexpectedly reached");
    assert(r.states === 1384, "unexpected closure size");
    assert(r.fnv64 === f.hashes[h], "closure fingerprint changed");
    console.log(f.name + " h=" + h +
      " start=(D=" + s.D + ",m=" + s.m + ",N0=" + s.N0 + ")" +
      " states=" + r.states + " root=" + r.rootReachable +
      " fnv64=" + r.fnv64);
  }
}
