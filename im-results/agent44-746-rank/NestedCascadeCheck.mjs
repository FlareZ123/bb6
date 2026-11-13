// Independent modular check of Agent 7's nested odd-parent branch.
// All arithmetic is exact BigInt and modular exponentiation.

const j = 3402n;
const r0 = 74803n;
const branchModulus = 3n ** 11n;
const nextModulus = 3n ** 12n;
const M = 3n ** 28n;
const ts = [7n, 1n, 0n, 2n, 1n, 0n];
const sigmas = [14n, 9n, 9n, 13n, 13n, 13n];

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
    v3X: valuationMod3(X, 28),
    v3G: valuationMod3(X, 28) - 2,
  }];
  let B = -(2n + 2n ** (j + 5n));
  const bMods = [String(mod(B, 3n))];

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
    Xs.push(X);
    Es.push(E);
    rows.push({
      i: i + 1,
      t: String(t),
      sigma: String(sigma),
      E: String(E),
      v3X: valuationMod3(X, 28),
      v3G: valuationMod3(X, 28) - Number(E),
    });
    bMods.push(String(mod(B, 3n)));
  }
  return { n, rows, bMods, Xs, Es };
}

function quotientMod3(value, exponent) {
  return mod(value / (3n ** exponent), 3n);
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

// Seventh edge: t=0, sigma=14, after the sixth (t=0, sigma=13) edge.
const [r7n, r7d] = reduce(gammaN * 2n ** 14n, gammaD * 3n);
const seventh = {
  t: 0,
  sigma: 14,
  ratio: String(r7n) + "/" + String(r7d),
  inside: 6n * r7d < r7n && r7n < 8n * r7d,
  decimal: Number(r7n) / Number(r7d),
};

const base = evaluate(r0, M);
const cylinderChecks = [];
for (let a = 0n; a < 3n; a++) {
  const r = r0 + branchModulus * a;
  const ev = evaluate(r, M);
  cylinderChecks.push({
    nextDigit: String(a),
    r: String(r),
    G5mod3: String(quotientMod3(ev.Xs[5], ev.Es[5])),
    G6mod3: String(quotientMod3(ev.Xs[6], ev.Es[6])),
  });
}

console.log(JSON.stringify({
  r0: String(r0),
  fiveEdgeCylinderModulus: String(branchModulus),
  sevenEdgeCylinderModulus: String(nextModulus),
  nAtRepresentative: String(base.n),
  valuationsAtRepresentative: base.rows,
  B_i_mod3: base.bMods,
  sixBandLimits: bandRows,
  seventhBandLimit: seventh,
  nextDigitChecks: cylinderChecks,
}, null, 2));
