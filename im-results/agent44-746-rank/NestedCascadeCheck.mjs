// Independent modular check of Agent 7's nested odd-parent branch
// through an explicit eighth edge. All arithmetic is exact BigInt.

const j = 3402n;
const r0 = 74803n;
const fiveEdgeModulus = 3n ** 11n;
const sevenEdgeModulus = 3n ** 12n;
const eightEdgeModulus = 3n ** 14n;
const M = 3n ** 30n;
const ts = [7n, 1n, 0n, 2n, 1n, 0n, 0n];
const sigmas = [14n, 9n, 9n, 13n, 13n, 13n, 14n];

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

function valuationMod3(x, limit) {
  let v = 0;
  while (v < limit && x % 3n === 0n) {
    x /= 3n;
    v++;
  }
  return v;
}

function bitLength(x) {
  return (x < 0n ? -x : x).toString(2).length;
}

function evaluate(r, modulus) {
  const n = 887n + 13122n * r;
  let E = 2n;
  let X = mod(
    28n * powMod(2n, n, modulus) - 2n * n + 15n
      - powMod(2n, j + 4n, modulus) * (2n * n + 3n),
    modulus
  );
  const Xs = [X];
  const Es = [E];
  const rows = [{
    i: 0,
    E: "2",
    v3X: valuationMod3(X, 30),
    v3G: valuationMod3(X, 30) - 2,
  }];
  let B = -(2n + 2n ** (j + 5n));
  let C = 15n - 3n * 2n ** (j + 4n);
  const bMods = [String(mod(B, 3n))];
  const coefficientBits = [{ i: 0, B: bitLength(B), C: bitLength(C) }];

  for (let i = 0; i < ts.length; i++) {
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
    B = 4n * (2n ** t) * B - 2n * 3n ** E;
    C = 4n * (2n ** t) * C - (2n * t - 2n * sigma + 5n) * 3n ** E;
    coefficientBits.push({ i: i + 1, B: bitLength(B), C: bitLength(C) });
    Xs.push(X);
    Es.push(E);
    rows.push({
      i: i + 1,
      t: String(t),
      sigma: String(sigma),
      E: String(E),
      v3X: valuationMod3(X, 30),
      v3G: valuationMod3(X, 30) - Number(E),
    });
    bMods.push(String(mod(B, 3n)));
  }
  return { n, rows, bMods, coefficientBits, Xs, Es };
}

function quotientMod(value, exponent, modulus) {
  return mod(value / (3n ** exponent), modulus);
}

function gcd(a, b) {
  return b === 0n ? a : gcd(b, a % b);
}

function reduce(n, d) {
  const g = gcd(n, d);
  return [n / g, d / g];
}

let gammaN = 28n;
let gammaD = 9n;
const bandRows = [];
for (let i = 0; i < ts.length; i++) {
  const t = ts[i];
  const sigma = sigmas[i];
  const [rn, rd] = reduce(gammaN * 2n ** sigma, gammaD * 3n ** (t + 1n));
  const inside = 6n * rd < rn && rn < 8n * rd;
  const [nextN, nextD] = reduce(
    4n * 2n ** t * (rn - 4n * rd),
    2n ** sigma * rd
  );
  bandRows.push({
    layer: i + 1,
    t: String(t),
    sigma: String(sigma),
    ratio: String(rn) + "/" + String(rd),
    inside,
    gammaNext: String(nextN) + "/" + String(nextD),
  });
  gammaN = nextN;
  gammaD = nextD;
}

// Eighth edge: t=1, sigma=17, after the seven listed layers.
const [r8n, r8d] = reduce(gammaN * 2n ** 17n, gammaD * 3n ** 2n);
const eighth = {
  t: 1,
  sigma: 17,
  ratio: String(r8n) + "/" + String(r8d),
  inside: 6n * r8d < r8n && r8n < 8n * r8d,
  decimal: Number(r8n) / Number(r8d),
};

const base = evaluate(r0, M);
const sevenDigitChecks = [];
for (let a = 0n; a < 3n; a++) {
  const r = r0 + fiveEdgeModulus * a;
  const ev = evaluate(r, M);
  sevenDigitChecks.push({
    nextDigit: String(a),
    r: String(r),
    G5mod3: String(quotientMod(ev.Xs[5], ev.Es[5], 3n)),
    G6mod3: String(quotientMod(ev.Xs[6], ev.Es[6], 3n)),
  });
}

const eighthDigitChecks = [];
for (let b = 0n; b < 9n; b++) {
  const r = r0 + sevenEdgeModulus * b;
  const ev = evaluate(r, M);
  eighthDigitChecks.push({
    nextDigit: String(b),
    r: String(r),
    G7mod9: String(quotientMod(ev.Xs[7], ev.Es[7], 9n)),
  });
}

console.log(JSON.stringify({
  r0: String(r0),
  fiveEdgeCylinderModulus: String(fiveEdgeModulus),
  sevenEdgeCylinderModulus: String(sevenEdgeModulus),
  eightEdgeCylinderModulus: String(eightEdgeModulus),
  nAtRepresentative: String(base.n),
  valuationsAtRepresentative: base.rows,
  B_i_mod3: base.bMods,
  coefficientBitLengths: base.coefficientBits,
  sevenBandLimits: bandRows,
  eighthBandLimit: eighth,
  sevenDigitChecks: sevenDigitChecks,
  eighthDigitChecks: eighthDigitChecks,
  eighthCylinderResidue: String(r0 + sevenEdgeModulus),
}, null, 2));
