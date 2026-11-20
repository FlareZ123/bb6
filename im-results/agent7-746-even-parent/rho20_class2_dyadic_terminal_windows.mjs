#!/usr/bin/env node
// Exact integer reproducer for the shifted rho-20 class-2 terminal windows.
// It counts all m with 810*2^s < 8192*(103+972m) < 837*2^s and
// checks the unchanged source residues under K -> K + 486m.

const ceilDiv = (a, b) => (a + b - 1n) / b;
const mod = (x, m) => ((x % m) + m) % m;

function powMod(base, exponent, modulus) {
  let x = 1n, b = base % modulus, e = exponent;
  while (e > 0n) {
    if ((e & 1n) !== 0n) x = (x * b) % modulus;
    b = (b * b) % modulus;
    e >>= 1n;
  }
  return x;
}

function windowFor(s) {
  const two = 1n << BigInt(s);
  const denominator = 8192n * 972n;
  const lower = 810n * two - 8192n * 103n;
  const upper = 837n * two - 8192n * 103n;
  const first = lower >= 0n ? lower / denominator + 1n : 0n;
  const last = ceilDiv(upper, denominator) - 1n;
  const count = last >= first ? last - first + 1n : 0n;
  if (count > 0n) {
    const g0 = 103n + 972n * first;
    const g1 = 103n + 972n * last;
    if (!(810n * two < 8192n * g0 && 8192n * g1 < 837n * two))
      throw new Error("window endpoint check failed at s=" + s);
  }
  return {s, first, last, count};
}

const a = 38n;
const windows = [];
let total = 0n;
for (let s = 19; s <= Number(a - 3n); s++) {
  const w = windowFor(s);
  windows.push(w);
  total += w.count;
}
if (total !== 233015n) throw new Error("unexpected a=38 count: " + total);

const residueRows = [];
for (const aRep of [38n, 92n, 146n]) {
  const m = 54n; // one exact s=19 witness; every other allowed m has the same residues
  const K0 = 97n * (1n << (aRep - 7n)) + 48n;
  const K = K0 + 486n * m;
  const g = 103n + 972n * m;
  const r = K + 4n - aRep;
  const p = powMod(2n, K, 243n);
  const q = powMod(2n, K - aRep, 243n);
  const rPow = powMod(2n, r, 243n);
  const B = mod((2n * K + 7n) * rPow, 243n);
  const Xnum81 = mod(80n * p + 2n * K + 13n - 2n * B, 81n);
  const X1num243 = mod(248n * p - 8n * B - 10n * K + 25n, 243n);
  const A9 = mod(4n * p + 2n * K + 1n, 9n);
  const Gnum243 = mod(256n * g * q + 74n * K - 23n, 243n);
  if (K % 54n !== 8n || K % 162n !== 116n || p !== 175n ||
      Xnum81 !== 54n || X1num243 !== 81n || A9 !== 6n || Gnum243 !== 0n)
    throw new Error("shifted modular certificate failed for a=" + aRep);
  residueRows.push({
    aMod162: String(aRep),
    KMod243: String(K % 243n),
    qMod243: String(q),
    twoToRMod243: String(rPow),
    BMod243: String(B),
    pMod243: String(p),
    XnumMod81: String(Xnum81),
    X1numMod243: String(X1num243),
    AMod9: String(A9),
    GnumMod243: String(Gnum243)
  });
}

process.stdout.write(JSON.stringify({
  a: "38",
  shiftedCandidates: String(total),
  byS: windows.map(w => ({
    s: w.s,
    firstM: String(w.first),
    lastM: String(w.last),
    count: String(w.count)
  })),
  modularRows: residueRows
}, null, 2) + "\n");
