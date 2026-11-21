#!/usr/bin/env node
// Exact modular certificate for six infinite a mod 486 classes in the
// rho-20, t=0, q=0 family. Uses BigInt only; no floating-point arithmetic.

const mod = (x, m) => ((x % m) + m) % m;

function powMod(base, exponent, modulus) {
  let b = mod(base, modulus);
  let e = exponent;
  let out = 1n;
  while (e > 0n) {
    if (e & 1n) out = (out * b) % modulus;
    b = (b * b) % modulus;
    e >>= 1n;
  }
  return out;
}

function residueData(a) {
  // K modulo 6561 is needed in the combined expressions below.
  const K6561 = mod(97n * powMod(2n, a - 7n, 6561n) + 48n, 6561n);
  // The exponent of 2 modulo 6561 has period 4374.
  const K4374 = mod(97n * powMod(2n, a - 7n, 4374n) + 48n, 4374n);
  const r4374 = mod(K4374 - a + 4n, 4374n);
  const p = powMod(2n, K4374, 6561n);
  const Q = powMod(2n, mod(K4374 - a, 4374n), 6561n);
  const twoR = powMod(2n, r4374, 6561n);
  const B = mod((2n * K6561 + 7n) * twoR, 6561n);

  // 3X = 80p + 2K + 13 - 2B, X = 2E+5.
  const threeX = mod(80n * p + 2n * K6561 + 13n - 2n * B, 6561n);
  if (threeX % 3n !== 0n) throw new Error("3X residue is not divisible by 3");
  const X2187 = threeX / 3n;

  // 9X1 = 248p - 8B - 10K + 25, X1 = 2h0+5.
  const nineX1 = mod(248n * p - 8n * B - 10n * K6561 + 25n, 6561n);
  if (nineX1 % 9n !== 0n) throw new Error("9X1 residue is not divisible by 9");
  const X1mod27 = (nineX1 / 9n) % 27n;

  // X2 = 16X/27 - 4p - 2K - 1, X2 = 2h2+5.
  if (X2187 % 27n !== 0n) throw new Error("X is not divisible by 27");
  const X2mod81 = mod(
    16n * (X2187 / 27n) - 4n * (p % 81n) - 2n * (K6561 % 81n) - 1n,
    81n
  );

  // X3 = 8X2/9 - p - 2K + 3, used only for the c=320 branch.
  let X3mod9 = null;
  let GprimeMod3 = null;
  if (X2mod81 % 9n === 0n) {
    X3mod9 = mod(
      8n * (X2mod81 / 9n) - (p % 9n) - 2n * (K6561 % 9n) + 3n,
      9n
    );
    // G' = p + 2K - 3 - 4X2/9.
    GprimeMod3 = mod(
      (p % 3n) + 2n * (K6561 % 3n) - 3n - 4n * (X2mod81 / 9n),
      3n
    );
  }

  // G = (26368 Q + 74 K - 23)/27, the h0-chain parameter.
  const Gnumerator243 = mod(
    26368n * (Q % 243n) + 74n * (K6561 % 243n) - 23n,
    243n
  );
  if (Gnumerator243 % 27n !== 0n) throw new Error("G numerator is not divisible by 27");
  const Gmod9 = Gnumerator243 / 27n;
  const Amod3 = mod(4n * (p % 3n) + 2n * (K6561 % 3n) + 1n, 3n);

  return {
    a: Number(a),
    X: Number(X2187),
    X1: Number(X1mod27),
    X2: Number(X2mod81),
    X3: X3mod9 === null ? "-" : Number(X3mod9),
    G: Number(Gmod9),
    A3: Number(Amod3),
    Gprime3: GprimeMod3 === null ? "-" : Number(GprimeMod3),
  };
}

function sameRelevantData(x, y) {
  return ["X", "X1", "X2", "X3", "G", "A3", "Gprime3"]
    .every((k) => x[k] === y[k]);
}

const classes = [50, 104, 212, 320, 374, 428];
const rows = [];
for (const c of classes) {
  for (let j = 0; j < 3; j++) {
    const a = BigInt(c + 486 * j);
    const row = residueData(a);
    const periodCheck = residueData(a + 1458n);
    if (!sameRelevantData(row, periodCheck)) {
      throw new Error(`derived residue period failed at a=${a}`);
    }
    rows.push({ class486: c, ...row });
  }
}

for (const row of rows) {
  if (row.X1 !== 21 || row.G !== 1 || row.A3 !== 0) {
    throw new Error(`common h0-chain residue failed: ${JSON.stringify(row)}`);
  }
  if (row.class486 === 320) {
    if (row.X2 % 9 !== 0 || row.X2 % 27 === 0 ||
        row.X3 % 3 === 0 || row.Gprime3 !== 0) {
      throw new Error(`c=320 branch residue failed: ${JSON.stringify(row)}`);
    }
  } else if (row.X2 % 3 !== 0 || row.X2 % 9 === 0) {
    throw new Error(`h2 leaf residue failed: ${JSON.stringify(row)}`);
  }
  if (row.class486 === 104 || row.class486 === 428) {
    if (row.X % 243 !== 0 || row.X % 729 === 0) {
      throw new Error(`c=${row.class486} must have v3(X)=5: ${JSON.stringify(row)}`);
    }
  } else if (row.X % 81 !== 0 || row.X % 243 === 0) {
    throw new Error(`class must have v3(X)=4: ${JSON.stringify(row)}`);
  }
}

console.log("Exact phase-50 modular certificate (all residues are least nonnegative):");
console.table(rows);
console.log("PASS: six a mod 486 classes; all three a mod 1458 lifts; period-1458 check; parent-valuation gates.");
