#!/usr/bin/env node
"use strict";

// Exact modular audit of the necessary condition
//   D_{w+2} | y + 2w + 3
// for the finite wide-band exception set in the cancellation family
// r = 110j + 50.  No giant integer 2^a is materialized: all calculations
// are exact BigInt modular arithmetic.

const r = BigInt(process.argv[2] || "50");
const primeLimit = Number(process.argv[3] || "1000000");
if (r < 50n || (r - 50n) % 110n !== 0n) {
  throw new Error("r must be 110*j+50 with j >= 0");
}
if (!Number.isSafeInteger(primeLimit) || primeLimit < 101) {
  throw new Error("prime limit must be an integer >= 101");
}

const j = (r - 50n) / 110n;
const a = (9n ** r + 5n) / 2n;
const n = 3n ** (2n * r - 1n);
const d = BigInt(n.toString(2).length);

function mod(x, m) {
  return ((x % m) + m) % m;
}

function powMod(base, exponent, modulus) {
  let x = mod(base, modulus);
  let e = exponent;
  let out = 1n;
  while (e > 0n) {
    if (e & 1n) out = (out * x) % modulus;
    x = (x * x) % modulus;
    e >>= 1n;
  }
  return out;
}

function inverseMod(a0, modulus) {
  let [t, newT] = [0n, 1n];
  let [r0, newR] = [modulus, mod(a0, modulus)];
  while (newR !== 0n) {
    const q = r0 / newR;
    [t, newT] = [newT, t - q * newT];
    [r0, newR] = [newR, r0 - q * newR];
  }
  if (r0 !== 1n) throw new Error("inverse does not exist");
  return mod(t, modulus);
}

// Return y mod m from 55*y = 8*A*P_r(A)+25, using the defining
// recurrence P_{i+1}=A^2 P_i + 9^i(A-3), modulo 55m.
function yMod(r0, a0, m) {
  const modulus = 55n * m;
  const A = powMod(2n, a0, modulus);
  const A2 = (A * A) % modulus;
  let P = 0n;
  let ninePower = 1n;
  for (let i = 0n; i < r0; i++) {
    P = mod(A2 * P + ninePower * (A - 3n), modulus);
    ninePower = (ninePower * 9n) % modulus;
  }
  const numerator = mod(8n * A * P + 25n, modulus);
  if (numerator % 55n !== 0n) {
    throw new Error("recurrence numerator lost its factor 55");
  }
  return numerator / 55n;
}

// Faster prime-modulus version for p>11, using Fermat to reduce the
// exponents before modular exponentiation.
function yModPrime(r0, a0, p) {
  if (p === 5n || p === 11n) return yMod(r0, a0, p);
  const A = powMod(2n, a0 % (p - 1n), p);
  const A2 = (A * A) % p;
  let P = 0n;
  let ninePower = 1n;
  for (let i = 0n; i < r0; i++) {
    P = mod(A2 * P + ninePower * (A - 3n), p);
    ninePower = (ninePower * 9n) % p;
  }
  const numerator = mod(8n * A * P + 25n, p);
  return (numerator * inverseMod(55n, p)) % p;
}

function* primesUpTo(limit) {
  const composite = new Uint8Array(limit + 1);
  for (let x = 2; x <= limit; x++) {
    if (composite[x]) continue;
    yield BigInt(x);
    if (x * x <= limit) {
      for (let y = x * x; y <= limit; y += x) composite[y] = 1;
    }
  }
}

const firstLevelPrimes = [
  5n, 7n, 11n, 13n, 19n, 29n, 37n, 61n, 67n, 79n, 101n
];
const yFirst = new Map(
  firstLevelPrimes.map(p => [p.toString(), yMod(r, a, p)])
);

const candidates = [];
for (let k = r - 1n; k <= 2n * r - 2n; k++) {
  for (let e = 0n; e <= d - 2n; e++) {
    const numerator = a - 5n - e;
    if (numerator % k !== 0n) continue;
    const s = numerator / k;
    if ((2n * r - 1n) * s < a) continue;
    if ((r - 1n) * s > a - d - 3n) continue;

    // Here e=c(s)-1, so c(s)<d and this is a wide-band exception.
    const w = a + s - 1n;
    let primePass = true;
    for (const p of firstLevelPrimes) {
      const Dmod = mod(powMod(2n, mod(w + 1n, p - 1n), p) + 3n, p);
      if (Dmod === 0n) {
        const beta = mod(
          3n * powMod(2n, mod(w, p - 1n), p) + w + 3n,
          p
        );
        if (yFirst.get(p.toString()) !== beta) {
          primePass = false;
          break;
        }
      }
    }
    if (!primePass) continue;

    const oddEntry =
      [1n, 2n, 15n].includes(w % 20n) ||
      w % 100n === mod(64n - 40n * j, 100n);
    if (!oddEntry) candidates.push({ k, e, s, w });
  }
}

const primeList = [...primesUpTo(primeLimit)];
const yCache = new Map();
const witnesses = [];
for (const candidate of candidates) {
  let witness = null;
  for (const p of primeList) {
    const exponent = mod(candidate.w + 3n, p - 1n);
    if (mod(powMod(2n, exponent, p) + 3n, p) !== 0n) continue;

    let y = yCache.get(p.toString());
    if (y === undefined) {
      y = yModPrime(r, a, p);
      yCache.set(p.toString(), y);
    }
    const targetResidue = mod(y + 2n * candidate.w + 3n, p);
    if (targetResidue !== 0n) {
      witness = { p: p.toString(), target_residue: targetResidue.toString() };
      break;
    }
  }
  witnesses.push({
    k: candidate.k.toString(),
    e: candidate.e.toString(),
    s: candidate.s.toString(),
    witness
  });
}

const eliminated = witnesses.filter(x => x.witness !== null);
const survivors = witnesses.filter(x => x.witness === null);
console.log(JSON.stringify({
  r: r.toString(),
  j: j.toString(),
  prime_limit: primeLimit,
  d: d.toString(),
  forced_even_exception_count: candidates.length,
  eliminated_by_offset_two_prime_filter: eliminated.length,
  survivors: survivors.map(x => ({ k: x.k, e: x.e })),
  witnesses: eliminated.map(x => ({
    k: x.k, e: x.e, p: x.witness.p,
    target_residue: x.witness.target_residue
  }))
}, null, 2));
