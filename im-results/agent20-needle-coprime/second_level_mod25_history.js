#!/usr/bin/env node
"use strict";

// Reproduce the finite modular calculations used in SecondLevelOddBlockFilter.md.
// This checks the five possible A residues, matrix powers, y mod 125, and the
// four mod-25 odd-block-length branches. It does not prove parent existence
// or blank-root reachability.

function assert(condition, message) {
  if (!condition) throw new Error(message);
}
function mod(a, m) {
  return ((a % m) + m) % m;
}
function powMod(a, e, m) {
  let r = 1n;
  a %= m;
  while (e > 0n) {
    if (e & 1n) r = (r * a) % m;
    a = (a * a) % m;
    e >>= 1n;
  }
  return r;
}
function invMod(a, m) {
  for (let x = 1n; x < m; x++) {
    if (mod(a * x, m) === 1n) return x;
  }
  throw new Error("nonunit in modular inverse");
}
function matMul(x, y, m) {
  return [
    [
      mod(x[0][0] * y[0][0] + x[0][1] * y[1][0], m),
      mod(x[0][0] * y[0][1] + x[0][1] * y[1][1], m)
    ],
    [
      mod(x[1][0] * y[0][0] + x[1][1] * y[1][0], m),
      mod(x[1][0] * y[0][1] + x[1][1] * y[1][1], m)
    ]
  ];
}
function matPow(x, e, m) {
  let r = [[1n, 0n], [0n, 1n]];
  while (e > 0n) {
    if (e & 1n) r = matMul(r, x, m);
    x = matMul(x, x, m);
    e >>= 1n;
  }
  return r;
}
function sameMatrix(a, b) {
  return a.every((row, i) => row.every((x, j) => x === b[i][j]));
}

const mod625 = 625n;
const expected50 = [[501n, 375n], [0n, 126n]];
const expected110 = [[476n, 75n], [0n, 276n]];

for (let j = 0n; j < 25n; j++) {
  const r = 110n * j + 50n;
  const z = powMod(9n, r, 1000n);
  const aMod500 = (z + 5n) / 2n;
  const A = powMod(2n, aMod500, mod625);
  assert(A === mod(8n + 375n * j, mod625), "A residue formula");

  const T = [[(A * A) % mod625, mod(A - 3n, mod625)], [0n, 9n]];
  assert(sameMatrix(matPow(T, 50n, mod625), expected50), "T(A)^50");
  assert(sameMatrix(matPow(T, 110n, mod625), expected110), "T(A)^110");

  const P = matPow(T, r, mod625)[0][1];
  assert(P === mod(375n + 75n * j, mod625), "P_r residue");
  const AP = (A * P) % mod625;
  assert(AP === mod(500n - 25n * j, mod625), "A*P residue");

  const y125 = mod(((8n * AP + 25n) / 5n) * invMod(11n, 125n), 125n);
  assert(y125 === mod(5n - 15n * j, 125n), "y mod 125");
  const y25 = mod(y125, 25n);

  const branches = [
    {
      base: 1n,
      expected: mod(61n - 40n * j, 100n),
      bFormula: m => mod(21n + 20n * j - 15n * m, 25n)
    },
    {
      base: 2n,
      expected: mod(2n + 60n * j, 100n),
      bFormula: m => mod(1n + 5n * j - 10n * m, 25n)
    },
    {
      base: 15n,
      expected: mod(95n - 40n * j, 100n),
      bFormula: m => mod(21n + 15n * j - 5n * m, 25n)
    }
  ];

  for (const branch of branches) {
    let lengthTwoCount = 0;
    for (let m = 0n; m < 5n; m++) {
      const w = branch.base + 20n * m;
      const twoToW = powMod(2n, w, 25n);
      const D = mod(powMod(2n, w + 1n, 25n) + 3n, 25n);
      const B = mod(3n * twoToW + w + 3n, 25n);
      const q = mod((y25 - B) * invMod(D, 25n), 25n);
      const b = mod(twoToW * (2n * q + 3n), 25n);
      assert(b === branch.bFormula(m), "first-three branch formula");
      const hasTwoOddSteps = b === 1n;
      assert(hasTwoOddSteps === (w % 100n === branch.expected),
        "first-three branch class");
      if (hasTwoOddSteps) lengthTwoCount++;
    }
    assert(lengthTwoCount === 1, "one mod-100 lift per branch");
  }

  const wTarget500 = mod(464n + 260n * j, 500n);
  let fourthBranchCount = 0;
  for (let m = 0n; m < 5n; m++) {
    const w0 = mod(64n - 40n * j, 100n);
    const w = w0 + 100n * m;
    const twoToW125 = powMod(2n, w, 125n);
    const D125 = mod(powMod(2n, w + 1n, 125n) + 3n, 125n);
    const B125 = mod(3n * twoToW125 + w + 3n, 125n);
    assert(D125 % 5n === 0n && D125 % 25n !== 0n, "v5(D_w)=1");
    const difference = mod(y125 - B125, 125n);
    assert(difference % 5n === 0n, "parent numerator divisible by 5");
    const q25 = mod((difference / 5n) * invMod(D125 / 5n, 25n), 25n);
    const b25 = mod(powMod(2n, w, 25n) * (2n * q25 + 3n), 25n);
    const hasTwoOddSteps = b25 === 1n;
    assert(hasTwoOddSteps === (w % 500n === wTarget500),
      "fourth branch class");
    if (hasTwoOddSteps) fourthBranchCount++;
  }
  assert(fourthBranchCount === 1, "one mod-500 lift in fourth branch");
}

console.log("Verified 25 values of j mod 25, all five A residues, both matrix powers, y mod 125, and all four mod-25 odd-block branches.");
