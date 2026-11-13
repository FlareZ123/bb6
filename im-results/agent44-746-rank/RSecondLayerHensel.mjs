// Exact modular reproduction of R-SECOND-LAYER-HENSEL.md.
// Node.js only; all arithmetic is BigInt and modular exponentiation.

const t = 7n;
const sigma = 14n;
const j = 3402n;
const n0 = 171473n;
const step = 354294n; // 6 * 3^10

const A = 7n * 2n ** sigma - 3n ** (t + 3n);
const B = -(2n ** (t + 3n) + 2n ** (j + t + 7n) + 2n * 3n ** (t + 3n));
const C =
  15n * 2n ** (t + 2n) -
  3n * 2n ** (j + t + 6n) -
  3n ** (t + 3n) * (2n * t - 2n * sigma + 5n);

function powMod(base, exponent, modulus) {
  let x = base % modulus;
  let e = exponent;
  let result = 1n;
  while (e > 0n) {
    if ((e & 1n) !== 0n) result = (result * x) % modulus;
    x = (x * x) % modulus;
    e >>= 1n;
  }
  return result;
}

function mod(value, modulus) {
  return ((value % modulus) + modulus) % modulus;
}

function Rmod(u, modulus) {
  const n = n0 + step * u;
  return mod(
    A * powMod(2n, n - 3n, modulus) + B * (n % modulus) + C,
    modulus
  );
}

const p3 = (k) => 3n ** BigInt(k);

console.log("A =", String(A));
console.log("B mod 3 =", String(mod(B, 3n)));
console.log("R mod 3^12 for u=0,1,2:");
for (let u = 0n; u < 3n; u++) {
  console.log(String(u), String(Rmod(u, p3(12))));
}

// Since B = 1 mod 3, the lift digit delta solves q + 2*delta = 0 mod 3,
// hence delta = q mod 3.
let rho = 0n;
console.log("Hensel residues rho_k (3^(11+k) | R iff u = rho_k mod 3^k):");
for (let k = 0; k < 15; k++) {
  const modulus = p3(12 + k);
  const divisor = p3(11 + k);
  const rem = Rmod(rho, modulus);
  if (rem % divisor !== 0n) {
    throw new Error("failed divisibility invariant at k=" + k);
  }
  const q = (rem / divisor) % 3n;
  const digit = q;
  rho += digit * p3(k);
  console.log(String(k + 1) + "\t" + String(rho) + "\tmod " + String(p3(k + 1)));
}

// Exact check of the least u=1 point in the ell=1 cylinder.
{
  const u = 1n;
  const n = n0 + step * u;
  const fullR = A * (2n ** (n - 3n)) + B * n + C;
  let quotient = fullR;
  let valuation = 0;
  while (quotient % 3n === 0n) {
    quotient /= 3n;
    valuation++;
  }
  const d = fullR / (3n ** 12n);
  const x = 2n * d;
  const kappa = n - 8n;
  const lower = 6n * (2n ** kappa);
  const upper = 8n * (2n ** kappa);
  console.log({
    firstEll1Point: true,
    n: String(n),
    v3R: valuation,
    quotientOdd: d % 2n === 1n,
    band: x > lower && x < upper,
  });
}

// Exact rational limits for three band-compatible further exponents.
console.log("Band-limit checks:");
for (const [ell, offset] of [[1n, 9n], [4n, 14n], [6n, 17n]]) {
  const numerator = A * 2n ** (offset - 3n);
  const denominator = p3(Number(ell + 11n));
  const inside = 6n * denominator < numerator && numerator < 8n * denominator;
  console.log({
    ell: String(ell),
    offset: String(offset),
    numerator: String(numerator),
    denominator: String(denominator),
    lower: String(6n * denominator),
    upper: String(8n * denominator),
    inside,
  });
}
