#!/usr/bin/env node
// Exact BigInt reproducer for shifted rho-20 terminal-window exclusions
// in phases a mod 54 = 14, 32, 38, 46.

const ceilDiv = (a, b) => (a + b - 1n) / b;
const mod = (x, m) => ((x % m) + m) % m;

function powMod(base, exponent, modulus) {
  let x = 1n, b = base % modulus, e = exponent;
  while (e > 0n) {
    if ((e & 1n) !== 0n) x = x * b % modulus;
    b = b * b % modulus;
    e >>= 1n;
  }
  return x;
}

function windowFor(s) {
  const two = 1n << BigInt(s);
  const den = 8192n * 972n;
  const lo = 810n * two - 8192n * 103n;
  const hi = 837n * two - 8192n * 103n;
  const first = lo / den + 1n;
  const last = ceilDiv(hi, den) - 1n;
  return {s, first, last, count: last >= first ? last - first + 1n : 0n};
}

function countForA(a) {
  let total = 0n;
  for (let s = 19; s <= a - 3; s++) total += windowFor(s).count;
  return total;
}

const expectedCounts = new Map([
  [32, 3639n],
  [38, 233015n],
  [46, 59652322n],
  [68, 250199979298359n]
]);
for (const [a, expected] of expectedCounts) {
  const actual = countForA(a);
  if (actual !== expected) throw new Error("count mismatch at a=" + a);
}

const phases = [
  {phase:14n, K162:152n, K54:44n, p:229n, X81:54n, X1:12n, A9:6n, Gnum:189n, X2:2n},
  {phase:32n, K162:44n,  K54:44n, p:67n,  X81:27n, X1:3n,  A9:6n, Gnum:108n, X2:1n},
  {phase:38n, K162:116n, K54:8n,  p:175n, X81:18n, X1:9n,  A9:6n, Gnum:0n,   X2:null},
  {phase:46n, K162:122n, K54:14n, p:22n,  X81:27n, X1:18n, A9:0n, Gnum:162n, X2:1n}
];

const residueRows = [];
for (const spec of phases) {
  for (let n = 0n; n < 3n; n++) {
    const a = spec.phase + 54n * n;
    const m = 54n; // exact witness for s=19
    const K0 = 97n * (1n << (a - 7n)) + 48n;
    const K = K0 + 486n * m;
    const g = 103n + 972n * m;
    const r = K + 4n - a;
    const p = powMod(2n, K, 243n);
    const q = powMod(2n, K - a, 243n);
    const rPow = powMod(2n, r, 243n);
    const B = mod((2n * K + 7n) * rPow, 243n);
    const threeX = mod(80n * p + 2n * K + 13n - 2n * B, 243n);
    const nineX1 = mod(248n * p - 8n * B - 10n * K + 25n, 243n);
    const X81 = threeX / 3n;
    const X27q = X81 / 27n;
    const A9 = mod(4n * p + 2n * K + 1n, 9n);
    const Gnum = mod(256n * g * q + 74n * K - 23n, 243n);
    const X2 = spec.X2 === null ? null :
      mod(16n * X27q - 4n * p - 2n * K - 1n, 3n);
    if (K % 162n !== spec.K162 || K % 54n !== spec.K54 ||
        mod(K + 6n * a, 54n) !== 20n || p !== spec.p ||
        X81 !== spec.X81 || nineX1 / 9n !== spec.X1 ||
        A9 !== spec.A9 || Gnum !== spec.Gnum ||
        (spec.X2 !== null && X2 !== spec.X2)) {
      throw new Error("modular row failed for phase=" + spec.phase + ", n=" + n);
    }
    residueRows.push({
      phase: String(spec.phase),
      a: String(a),
      KMod243: String(K % 243n),
      qMod243: String(q),
      twoToRMod243: String(rPow),
      BMod243: String(B),
      pMod243: String(p),
      XMod81: String(X81),
      X1Mod27: String(nineX1 / 9n),
      AMod9: String(A9),
      GnumMod243: String(Gnum),
      X2Mod3: X2 === null ? "not applicable" : String(X2)
    });
  }
}

process.stdout.write(JSON.stringify({
  exactCounts: Object.fromEntries([...expectedCounts].map(([a,n])=>[a,String(n)])),
  s19Witnesses: [54,55],
  modularRows: residueRows
}, null, 2) + "\n");
