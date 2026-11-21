#!/usr/bin/env node
// Exact finite check of the 162-shift third-lift reduction in
// T0-K3-ODD-A-THIRD-LIFT.md. It checks all odd a mod162 and the
// three K mod486 lifts of each high K mod162 class.

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

function numeratorMod(a, K, modulus, exponentPeriod) {
  const p = pow2Mod(K, modulus);
  const b = mod(
    (2 * K + 7) * pow2Mod(mod(K + 4 - a, exponentPeriod), modulus),
    modulus
  );
  return mod(80 * p + 2 * K + 13 - 2 * b, modulus);
}

function xMod27(a, K) {
  const t = numeratorMod(a, K, 81, 54);
  if (t % 3 !== 0) throw new Error("X numerator not divisible by 3 mod 81");
  return mod(t / 3, 27);
}

function xMod81(a, K) {
  const t = numeratorMod(a, K, 243, 162);
  if (t % 3 !== 0) throw new Error("X numerator not divisible by 3 mod 243");
  return mod(t / 3, 81);
}

let checked = 0;
for (let a = 1; a < 162; a += 2) {
  const a18 = a % 18;

  // Locate the unique high K mod162 lift in the X == 0 (mod 9) phase.
  const k0 = mod(12 - 3 * a18, 54);
  const x0 = [0, 1, 2].map(m => xMod27(a, k0 + 54 * m));
  if (x0.slice().sort((u, v) => u - v).join(",") !== "0,9,18") {
    throw new Error("X0 second-lift table failed for a=" + a);
  }
  const k0High = k0 + 54 * x0.indexOf(0);

  // Locate the unique high K mod162 lift in the X == 3 (mod 9) phase.
  const k1 = mod(48 - 3 * a18, 54);
  const h3 = [0, 1, 2].map(m => {
    const K = k1 + 54 * m;
    const x27 = xMod27(a, K);
    if (!(x27 === 3 || x27 === 12 || x27 === 21)) {
      throw new Error("X3 phase table failed for a=" + a);
    }
    const d9 = mod(x27 / 3, 9);
    return mod(2 * d9 - 4 * pow2Mod(K, 9) - K - 4, 9);
  });
  if (h3.slice().sort((u, v) => u - v).join(",") !== "2,5,8") {
    throw new Error("h second-lift table failed for a=" + a);
  }
  const k1High = k1 + 54 * h3.indexOf(2);

  // The three K mod486 lifts of the X0 high class have X mod81 = 0,27,54.
  const x0Third = [0, 1, 2].map(m => xMod81(a, k0High + 162 * m));
  if (x0Third.slice().sort((u, v) => u - v).join(",") !== "0,27,54") {
    throw new Error("X0 third-lift table failed for a=" + a);
  }

  // The three K mod486 lifts of the X3 high class have Y mod27 = 0,9,18.
  const y3Third = [0, 1, 2].map(m => {
    const K = k1High + 162 * m;
    const x81 = xMod81(a, K);
    const d27 = mod(x81 / 3, 27);
    const h27 = mod(2 * d27 - 4 * pow2Mod(K, 27) - K - 4, 27);
    return mod(2 * h27 + 5, 27);
  });
  if (y3Third.slice().sort((u, v) => u - v).join(",") !== "0,9,18") {
    throw new Error("X3 third-lift table failed for a=" + a);
  }

  checked++;
}

console.log("PASS: second- and third-lift permutations for all " + checked + " odd a mod162 values.");
