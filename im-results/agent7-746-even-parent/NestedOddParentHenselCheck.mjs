// Exact modular reproduction of the four-edge nested odd-parent branch.
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
const r = 15754n;
const n = 887n + 13122n * r;

// Q_3402(n) modulo 3^17 is enough to recover the successive quotients.
const qmod = mod(
  28n * powMod(2n, n, p3(17))
    - 2n * n + 15n
    - powMod(2n, 3406n, p3(17)) * (2n * n + 3n),
  p3(17)
);
if (qmod % p3(10) !== 0n || qmod % p3(11) === 0n) {
  throw new Error("Q does not have exact 3-adic valuation 10");
}
const d1 = qmod / p3(10);

// (t_1, sigma_1) = (7,14), k_1 = n-7.
const g1 = mod(
  powMod(2n, 9n, p3(7)) * d1
    - 16n * powMod(2n, n - 7n, p3(7))
    - 2n * (n - 7n) - 5n,
  p3(7)
);
if (g1 % p3(2) !== 0n || g1 % p3(3) === 0n) {
  throw new Error("G1 does not have exact 3-adic valuation 2");
}
const d2 = g1 / p3(2);

// (t_2, sigma_2) = (1,9), k_2 = n-8.
const g2 = mod(
  powMod(2n, 3n, p3(5)) * d2
    - 16n * powMod(2n, n - 8n, p3(5))
    - 2n * (n - 8n) - 5n,
  p3(5)
);
if (g2 % 3n !== 0n || g2 % 9n === 0n) {
  throw new Error("G2 does not have exact 3-adic valuation 1");
}
const d3 = g2 / 3n;

// (t_3, sigma_3) = (0,9), k_3 = n-9.
const g3 = mod(
  powMod(2n, 2n, p3(4)) * d3
    - 16n * powMod(2n, n - 9n, p3(4))
    - 2n * (n - 9n) - 5n,
  p3(4)
);
if (g3 !== 0n) {
  throw new Error("G3 is not divisible by 3^4");
}
const d4 = g3 / 27n;

// (t_4, sigma_4) = (2,13), k_4 = n-11.
// Since G3 is known modulo 3^4, d4 is known modulo 3.
const g4mod3 = mod(
  powMod(2n, 4n, 3n) * d4
    - 16n * powMod(2n, n - 11n, 3n)
    - 2n * (n - 11n) - 5n,
  3n
);
if (g4mod3 !== 0n) {
  throw new Error("G4 is not divisible by 3");
}

const output = {
  r: r.toString(),
  modulus: "19683",
  n: n.toString(),
  Qmod3pow17: qmod.toString(),
  v3Q: 10,
  G1mod3pow7: g1.toString(),
  v3G1: 2,
  G2mod3pow5: g2.toString(),
  v3G2: 1,
  G3mod81: g3.toString(),
  v3G3: "at least 4",
  G4mod3: g4mod3.toString(),
  exponents: [[7, 14], [1, 9], [0, 9], [2, 13]]
};
console.log(JSON.stringify(output, null, 2));
