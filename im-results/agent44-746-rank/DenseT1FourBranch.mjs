// Exact modular reproducer for DENSE-T1-4-CASCADE.md.
// All arithmetic is BigInt; exponentiation is modular except for small coefficients.

const j = 3402n;
const ts = [4n, 0n, 0n, 1n, 3n];
const sigmas = [9n, 6n, 7n, 9n, 14n];

function powMod(a, e, m) {
  let x = a % m;
  let y = 1n;
  while (e > 0n) {
    if (e & 1n) y = (y * x) % m;
    x = (x * x) % m;
    e >>= 1n;
  }
  return y;
}

function mod(x, m) {
  return ((x % m) + m) % m;
}

function evaluateXs(r, modulus, layers) {
  const n = 887n + 13122n * r;
  let E = 2n;
  let X = mod(
    28n * powMod(2n, n, modulus) - 2n * n + 15n
      - powMod(2n, j + 4n, modulus) * (2n * n + 3n),
    modulus
  );
  const Xs = [X];
  const Es = [E];
  for (let i = 0; i < layers; i++) {
    const t = ts[i];
    const sigma = sigmas[i];
    const k = n + t - sigma;
    E += t + 1n;
    X = mod(
      4n * (2n ** t) * X
        - 16n * powMod(2n, k, modulus) * 3n ** E
        - (2n * k + 5n) * 3n ** E,
      modulus
    );
    Xs.push(X);
    Es.push(E);
  }
  return { n, Xs, Es };
}

function quotientMod(x, e, m) {
  return mod(x / (3n ** e), m);
}

function valuationMod3(x, limit) {
  let v = 0;
  while (v < limit && x % 3n === 0n) {
    x /= 3n;
    v++;
  }
  return v;
}

function gcd(a, b) {
  return b === 0n ? a : gcd(b, a % b);
}

function reduce(a, b) {
  const g = gcd(a, b);
  return [a / g, b / g];
}

function bitLength(x) {
  return (x < 0n ? -x : x).toString(2).length;
}

// First digit: G2 mod 3 for r=0,1,2.
const firstDigit = [];
for (let r = 0n; r < 3n; r++) {
  const ev = evaluateXs(r, 3n ** 9n, 2);
  firstDigit.push({
    r: String(r),
    G2mod3: String(quotientMod(ev.Xs[2], ev.Es[2], 3n)),
  });
}

// Second selector: G3 mod 9 for r=1+3u, u=0,...,8.
const secondDigit = [];
for (let u = 0n; u < 9n; u++) {
  const r = 1n + 3n * u;
  const ev = evaluateXs(r, 3n ** 11n, 4);
  secondDigit.push({
    u: String(u),
    r: String(r),
    G3mod9: String(quotientMod(ev.Xs[3], ev.Es[3], 9n)),
  });
}

// Third selector: G4 mod 81 for r=25+27u, u=0,...,80.
let fifthRoot = null;
for (let u = 0n; u < 81n; u++) {
  const r = 25n + 27n * u;
  const ev = evaluateXs(r, 3n ** 15n, 5);
  if (quotientMod(ev.Xs[4], ev.Es[4], 81n) === 0n) {
    fifthRoot = { u: String(u), r: String(r) };
  }
}

// Representative valuations at r=1618.
const representative = 1618n;
const rep = evaluateXs(representative, 3n ** 20n, 5);
const valuations = rep.Xs.map((x, i) => ({
  i,
  E: String(rep.Es[i]),
  v3X: valuationMod3(x, 20),
  v3G: valuationMod3(x, 20) - Number(rep.Es[i]),
}));

// Exact B_i,C_i coefficient bit lengths.
let E = 2n;
let B = -(2n + 2n ** (j + 5n));
let C = 15n - 3n * 2n ** (j + 4n);
const coefficientBits = [{ i: 0, B: bitLength(B), C: bitLength(C) }];
for (let i = 0; i < ts.length; i++) {
  const t = ts[i];
  const sigma = sigmas[i];
  E += t + 1n;
  B = 4n * (2n ** t) * B - 2n * 3n ** E;
  C = 4n * (2n ** t) * C - (2n * t - 2n * sigma + 5n) * 3n ** E;
  coefficientBits.push({ i: i + 1, B: bitLength(B), C: bitLength(C) });
}

// Exact limiting band ratios and gamma recurrence.
let gammaN = 28n;
let gammaD = 9n;
const bandLimits = [];
for (let i = 0; i < ts.length; i++) {
  const t = ts[i];
  const sigma = sigmas[i];
  const [rn, rd] = reduce(gammaN * 2n ** sigma, gammaD * 3n ** (t + 1n));
  const [nextN, nextD] = reduce(
    4n * (2n ** t) * (rn - 4n * rd),
    2n ** sigma * rd
  );
  bandLimits.push({
    layer: i + 1,
    t: String(t),
    sigma: String(sigma),
    numerator: String(rn),
    denominator: String(rd),
    inside: 6n * rd < rn && rn < 8n * rd,
    decimal: Number(rn) / Number(rd),
    gammaNext: String(nextN) + "/" + String(nextD),
  });
  gammaN = nextN;
  gammaD = nextD;
}

console.log(JSON.stringify({
  firstDigit,
  secondDigit,
  fifthRoot,
  representative: String(representative),
  n: String(rep.n),
  valuations,
  coefficientBits,
  bandLimits,
}, null, 2));
