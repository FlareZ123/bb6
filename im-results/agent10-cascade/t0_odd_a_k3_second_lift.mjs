#!/usr/bin/env node
// Exact finite check of the modulo-81 second-lift tables in
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

const expectedX0 = {
  0: [3, 5, 7, 15, 27, 35, 37, 47, 49],
  9: [9, 17, 19, 29, 31, 39, 41, 43, 51],
  18: [1, 11, 13, 21, 23, 25, 33, 45, 53]
};
const expectedH3 = {
  2: [1, 3, 5, 17, 31, 33, 43, 45, 47],
  5: [7, 9, 11, 19, 21, 23, 35, 49, 51],
  8: [13, 15, 25, 27, 29, 37, 39, 41, 53]
};

const actualX0 = { 0: [], 9: [], 18: [] };
const actualH3 = { 2: [], 5: [], 8: [] };

for (let a = 1; a < 54; a += 2) {
  const a18 = a % 18;

  // X == 0 (mod 9) phase: K == 12 - 3a (mod 54).
  const k0 = mod(12 - 3 * a18, 54);
  const p0 = pow2Mod(k0, 81);
  const b0 = mod(
    (2 * k0 + 7) * pow2Mod(mod(k0 + 4 - a, 54), 81),
    81
  );
  const t0 = mod(80 * p0 + 2 * k0 + 13 - 2 * b0, 81);
  if (t0 % 3 !== 0) throw new Error("X0 numerator is not divisible by 3");
  const x27 = mod(t0 / 3, 27);
  if (!(x27 === 0 || x27 === 9 || x27 === 18)) {
    throw new Error("X0 lift is not 0, 9, or 18 modulo 27");
  }
  actualX0[x27].push(a);

  // X == 3 (mod 9) phase: K == 48 - 3a (mod 54).
  const k3 = mod(48 - 3 * a18, 54);
  const p3_81 = pow2Mod(k3, 81);
  const b3 = mod(
    (2 * k3 + 7) * pow2Mod(mod(k3 + 4 - a, 54), 81),
    81
  );
  const t3 = mod(80 * p3_81 + 2 * k3 + 13 - 2 * b3, 81);
  if (t3 % 3 !== 0) throw new Error("X3 numerator is not divisible by 3");
  const x3_27 = mod(t3 / 3, 27);
  if (!(x3_27 === 3 || x3_27 === 12 || x3_27 === 21)) {
    throw new Error("X3 lift is not 3, 12, or 21 modulo 27");
  }
  const d9 = mod(x3_27 / 3, 9);
  const p3_9 = pow2Mod(k3, 9);
  const h9 = mod(2 * d9 - 4 * p3_9 - k3 - 4, 9);
  if (!(h9 === 2 || h9 === 5 || h9 === 8)) {
    throw new Error("h lift is not 2, 5, or 8 modulo 9");
  }
  actualH3[h9].push(a);
}

for (const key of [0, 9, 18]) {
  if (actualX0[key].join(",") !== expectedX0[key].join(",")) {
    throw new Error("Unexpected X0 lift set for residue " + key);
  }
}
for (const key of [2, 5, 8]) {
  if (actualH3[key].join(",") !== expectedH3[key].join(",")) {
    throw new Error("Unexpected h lift set for residue " + key);
  }
}

console.log("X == 0 (mod 9) phase, X mod 27:");
for (const key of [0, 9, 18]) console.log(key + ": " + actualX0[key].join(", "));
console.log("X == 3 (mod 9) phase, h mod 9:");
for (const key of [2, 5, 8]) console.log(key + ": " + actualH3[key].join(", "));
console.log("PASS: all 27 odd a-residues in both second-lift tables.");
