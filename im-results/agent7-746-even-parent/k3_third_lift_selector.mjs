#!/usr/bin/env node
// Exact finite modular audit of the all-a K3 third-lift selector.
// This checks the residue identities used in K3-HIGH-Y-ARBITRARY-DEPTH.md.
// All calculations are BigInt modular arithmetic; no floating point.

const mod = (n, m) => ((n % m) + m) % m;

function pow2(e, m) {
  let v = 1n, b = 2n % m;
  while (e > 0n) {
    if (e & 1n) v = v * b % m;
    b = b * b % m;
    e >>= 1n;
  }
  return v;
}

function Tmod(a, K, modulus, period) {
  const e = mod(K + 4n - a, period);
  return mod(
    80n * pow2(K, modulus) + 2n * K + 13n
      - 2n * mod((2n * K + 7n) * pow2(e, modulus), modulus),
    modulus
  );
}

function highXClass(a) {
  const K1 = mod(48n - 3n * a, 54n);
  const candidates = [];
  for (let j = 0n; j < 3n; j++) {
    const K = K1 + 54n * j;
    const T81 = Tmod(a, K, 81n, 54n);
    if (T81 % 9n !== 0n) throw new Error("X phase division failed");
    const X27 = T81 / 3n;
    const h9 = mod(2n * (X27 / 3n) - 4n * pow2(K, 9n) - K - 4n, 9n);
    candidates.push({ K, h9 });
  }
  const selected = candidates.filter(q => q.h9 === 2n);
  if (selected.length !== 1) throw new Error(`high-X selector not unique for a=${a}`);
  return selected[0].K;
}

function thirdLifts(a, Kstar) {
  const rows = [];
  for (let j = 0n; j < 3n; j++) {
    const K = Kstar + 162n * j;
    const T243 = Tmod(a, K, 243n, 162n);
    if (T243 % 9n !== 0n) throw new Error("X high phase division failed");
    const X81 = T243 / 3n;
    const h27 = mod(2n * (X81 / 3n) - 4n * pow2(K, 27n) - K - 4n, 27n);
    const Y27 = mod(2n * h27 + 5n, 27n);
    if (Y27 % 9n !== 0n) throw new Error("Y is not divisible by 9");
    const g9 = Y27 / 3n;
    const G9 = mod(2n * g9 - 2n * pow2(K, 9n) - K - 3n, 9n);
    const Z9 = mod(2n * G9 + 5n, 9n);
    rows.push({ j: Number(j), Kmod486: mod(K, 486n), Y27, Z9 });
  }
  return rows;
}

const rows = [];
const summary = {
  aResidues: 0,
  selectedHighY: 0,
  selectedNonHighY: 0,
  selectedNonHighByAMod3: { 0: 0, 1: 0, 2: 0 },
  highYFormulaChecks: 0
};

for (let a = 1n; a < 162n; a += 2n) {
  const Kstar = highXClass(a);
  const lifts = thirdLifts(a, Kstar);
  const ySet = lifts.map(q => q.Y27.toString()).sort().join(",");
  const zSet = lifts.map(q => q.Z9.toString()).sort().join(",");
  if (ySet !== "0,18,9" || zSet !== "0,3,6") {
    throw new Error(`third-lift cycles failed for a=${a}: Y=${ySet}, Z=${zSet}`);
  }
  const highY = lifts.find(q => q.Y27 === 0n);
  const expectedHighYZ = mod(3n * (2n * a - 1n), 9n);
  if (highY.Z9 !== expectedHighYZ) {
    throw new Error(`high-Y Z formula failed for a=${a}`);
  }
  summary.aResidues++;
  summary.highYFormulaChecks++;
  const selected = lifts.find(q => q.Z9 === 0n);
  if (!selected) throw new Error(`no 9-divisible Z lift for a=${a}`);
  const aMod3 = Number(a % 3n);
  if (selected.Y27 === 0n) {
    summary.selectedHighY++;
  } else {
    summary.selectedNonHighY++;
    summary.selectedNonHighByAMod3[aMod3]++;
  }
  rows.push({
    a: Number(a),
    aMod3,
    KstarMod162: Number(Kstar),
    selectedKmod486: Number(selected.Kmod486),
    selectedYmod27: Number(selected.Y27),
    highYZmod9: Number(highY.Z9)
  });
}

if (summary.selectedHighY !== 27 || summary.selectedNonHighY !== 54) {
  throw new Error("unexpected all-a split");
}
if (summary.selectedNonHighByAMod3[0] !== 27
    || summary.selectedNonHighByAMod3[1] !== 27
    || summary.selectedNonHighByAMod3[2] !== 0) {
  throw new Error("unexpected a mod 3 classification");
}

console.log(JSON.stringify({ summary, rows }, null, 2));
