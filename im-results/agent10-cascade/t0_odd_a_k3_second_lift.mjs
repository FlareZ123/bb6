#!/usr/bin/env node
// Exact finite check of the K mod 162 second-lift table in
// T0-K3-ODD-A-SECOND-LIFT.md. This checks residue arithmetic only;
// the dyadic interval and ResetParent gap proofs are in the Markdown note.

const mod = (x, m) => ((x % m) + m) % m;

function pow2Mod(exponent, modulus) {
  let e = BigInt(exponent);
  const m = BigInt(modulus);
  let base = 2n % m;
  let value = 1n;
  while (e > 0n) {
    if (e & 1n) value = (value * base) % m;
    base = (base * base) % m;
    e >>= 1n;
  }
  return Number(value);
}

function xMod27(a, K) {
  const p81 = pow2Mod(K, 81);
  const b81 = mod(
    (2 * K + 7) * pow2Mod(mod(K + 4 - a, 54), 81),
    81
  );
  const numerator81 = mod(80 * p81 + 2 * K + 13 - 2 * b81, 81);
  if (numerator81 % 3 !== 0) {
    throw new Error("The numerator defining X is not divisible by 3.");
  }
  return mod(numerator81 / 3, 27);
}

const rows = [];
for (let a = 1; a < 54; a += 2) {
  const a18 = a % 18;
  const k0 = mod(12 - 3 * a18, 54);
  const x0 = [];
  for (let m = 0; m < 3; m++) x0.push(xMod27(a, k0 + 54 * m));
  if (x0.slice().sort((u, v) => u - v).join(",") !== "0,9,18") {
    throw new Error("X0 lifts are not a permutation of 0,9,18.");
  }
  const m0 = x0.indexOf(0);

  const k1 = mod(48 - 3 * a18, 54);
  const h3 = [];
  for (let m = 0; m < 3; m++) {
    const K = k1 + 54 * m;
    const x27 = xMod27(a, K);
    if (!(x27 === 3 || x27 === 12 || x27 === 21)) {
      throw new Error("X3 lift is not 3,12,21 modulo 27.");
    }
    const d9 = mod(x27 / 3, 9);
    const h9 = mod(2 * d9 - 4 * pow2Mod(K, 9) - K - 4, 9);
    h3.push(h9);
  }
  if (h3.slice().sort((u, v) => u - v).join(",") !== "2,5,8") {
    throw new Error("h lifts are not a permutation of 2,5,8.");
  }
  const m1 = h3.indexOf(2);
  rows.push({ a, k0, x0, m0, k1, h3, m1 });
}

console.log("a | K0 | X mod 27 on K0+54m | m0 | K1 | h mod 9 on K1+54m | m1");
for (const r of rows) {
  console.log(
    [r.a, r.k0, "(" + r.x0.join(",") + ")", r.m0,
      r.k1, "(" + r.h3.join(",") + ")", r.m1].join(" | ")
  );
}
console.log("PASS: all 27 a residues and all 162 second-lift entries.");
