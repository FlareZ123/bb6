// Independent modular check of Agent 7's five-edge branch and
// the immediate sixth t=0 parent. All arithmetic is exact BigInt.

const j = 3402n;
const r0 = 74803n;
const branchModulus = 3n ** 11n;
const M = 3n ** 28n;
const ts = [7n, 1n, 0n, 2n, 1n];
const sigmas = [14n, 9n, 9n, 13n, 13n];

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
  return { n, rows, bMods, X5: X, E5: E };
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

// Sixth edge: t=0, sigma=13.
const [r6n, r6d] = reduce(gammaN * 2n ** 13n, gammaD * 3n);
const sixth = {
  t: 0,
  sigma: 13,
  ratio: String(r6n) + "/" + String(r6d),
  inside: 6n * r6d < r6n && r6n < 8n * r6d,
  decimal: Number(r6n) / Number(r6d),
};

// Check the representative and the next member of its residue cylinder.
// E5=18 and B5 is a unit, so the scaled shift law fixes G5 mod 3
// when r changes by 3^11 (n changes by 6*3^18).
const base = evaluate(r0, M);
const next = evaluate(r0 + branchModulus, M);
const G5mod3 = (X) => mod(X / (3n ** 18n), 3n);

console.log(JSON.stringify({
  r0: String(r0),
  branchModulus: String(branchModulus),
  n: String(base.n),
  valuationsAtRepresentative: base.rows,
  B_i_mod3: base.bMods,
  fiveBandLimits: bandRows,
  sixthBandLimit: sixth,
  G5mod3AtR0: String(G5mod3(base.X5)),
  G5mod3AtNextCylinderPoint: String(G5mod3(next.X5)),
}, null, 2));
