// Exact modular reproduction of the five-edge nested odd-parent branch.
// No large 2^n integer is constructed; all exponentiation is modular BigInt.
const mod = (x, m) => ((x % m) + m) % m;

function powMod(base, exp, modulus) {
  let x = base % modulus;
  let e = exp;
  let out = 1n;
  while (e > 0n) {
    if ((e & 1n) !== 0n) out = (out * x) % modulus;
    x = (x * x) % modulus;
    e >>= 1n;
  }
  return out;
}

const p3 = k => 3n ** BigInt(k);
const r = 74803n;
const n = 887n + 13122n * r;

// Q_3402(n) modulo 3^19 is enough to recover G_1,...,G_5.
const qmod = mod(
  28n * powMod(2n, n, p3(19))
    - 2n * n + 15n
    - powMod(2n, 3406n, p3(19)) * (2n * n + 3n),
  p3(19)
);
if (qmod % p3(10) !== 0n || qmod % p3(11) === 0n) {
  throw new Error("Q does not have exact 3-adic valuation 10");
}
const d1 = qmod / p3(10);

// (t_1, sigma_1) = (7,14), k_1 = n-7.
const g1 = mod(
  512n * d1
    - 16n * powMod(2n, n - 7n, p3(9))
    - 2n * (n - 7n) - 5n,
  p3(9)
);
if (g1 % p3(2) !== 0n || g1 % p3(3) === 0n) {
  throw new Error("G1 does not have exact 3-adic valuation 2");
}
const d2 = g1 / p3(2);

// (t_2, sigma_2) = (1,9), k_2 = n-8.
const g2 = mod(
  8n * d2
    - 16n * powMod(2n, n - 8n, p3(7))
    - 2n * (n - 8n) - 5n,
  p3(7)
);
if (g2 % 3n !== 0n || g2 % 9n === 0n) {
  throw new Error("G2 does not have exact 3-adic valuation 1");
}
const d3 = g2 / 3n;

// (t_3, sigma_3) = (0,9), k_3 = n-9.
const g3 = mod(
  4n * d3
    - 16n * powMod(2n, n - 9n, p3(6))
    - 2n * (n - 9n) - 5n,
  p3(6)
);
if (g3 % p3(4) !== 0n) {
  throw new Error("G3 is not divisible by 3^4");
}
const d4 = g3 / 27n;

// (t_4, sigma_4) = (2,13), k_4 = n-11.
const g4 = mod(
  16n * d4
    - 16n * powMod(2n, n - 11n, p3(3))
    - 2n * (n - 11n) - 5n,
  p3(3)
);
if (g4 % 9n !== 0n || g4 % 27n === 0n) {
  throw new Error("G4 does not have exact 3-adic valuation 2");
}
const d5 = g4 / 9n;

// (t_5, sigma_5) = (1,13), k_5 = n-12.
const g5mod3 = mod(
  8n * d5
    - 16n * powMod(2n, n - 12n, 3n)
    - 2n * (n - 12n) - 5n,
  3n
);
if (g5mod3 !== 0n) {
  throw new Error("G5 is not divisible by 3");
}

const bitLength = x => (x < 0n ? -x : x).toString(2).length;
const coefficientBits = [];
let coeffB = -2n - (1n << 3407n);
let coeffC = 15n - 3n * (1n << 3406n);
coefficientBits.push({level:0, B:bitLength(coeffB), C:bitLength(coeffC)});
let cumulativeE = 0;
const stages = [[7,14],[1,9],[0,9],[2,13],[1,13]];
for (let i = 0; i < stages.length; i++) {
  const [t,sigma] = stages[i];
  cumulativeE = i === 0 ? t + 3 : cumulativeE + t + 1;
  coeffB = 4n * (1n << BigInt(t)) * coeffB - 2n * p3(cumulativeE);
  coeffC = 4n * (1n << BigInt(t)) * coeffC
    - (2n * BigInt(t - sigma) + 5n) * p3(cumulativeE);
  coefficientBits.push({level:i+1, B:bitLength(coeffB), C:bitLength(coeffC)});
}
if (coefficientBits.slice(0,5).some(x => x.B > 3426 || x.C > 3426)) {
  throw new Error("Unexpected coefficient bound for the five band estimates");
}

const limitingRatios = [
  [458752n, 59049n],
  [3560896n, 531441n],
  [11481056n, 1594323n],
  [326640896n, 43046721n],
  [2471264192n, 387420489n]
];
for (const [num,den] of limitingRatios) {
  if (5n*num <= 31n*den || 10n*num >= 79n*den) {
    throw new Error("A limiting band ratio is outside (6.2,7.9)");
  }
}
const bandParameters = [[7,14],[1,9],[0,9],[2,13],[1,13]];
for (const [t,sigma] of bandParameters) {
  if ((1n << BigInt(sigma)) >= p3(t+1) * 1024n) {
    throw new Error("A band scaling factor is not below 2^10");
  }
}
if (n < 7000n) throw new Error("The explicit index is below the band-bound threshold");

const output = {
  r: r.toString(),
  modulus: "177147",
  n: n.toString(),
  v3Q: 10,
  G1mod3pow9: g1.toString(),
  v3G1: 2,
  G2mod3pow7: g2.toString(),
  v3G2: 1,
  G3mod3pow6: g3.toString(),
  v3G3: "at least 4",
  G4mod3pow3: g4.toString(),
  v3G4: 2,
  G5mod3: g5mod3.toString(),
  exponents: [[7, 14], [1, 9], [0, 9], [2, 13], [1, 13]],
  coefficientBitLengths: coefficientBits,
  limitingBandRatios: limitingRatios.map(([num,den]) => ({num:num.toString(),den:den.toString()})),
  bandBound: "for n >= 7000, all five normalized ratios differ from their limits by < 2^-60"
};
console.log(JSON.stringify(output, null, 2));
