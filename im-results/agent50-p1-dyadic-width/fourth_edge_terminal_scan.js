"use strict";

// Exact BigInt scan for the four-edge terminal equation in the P1 restart wall.
// This classifies the 3 branches x 3^3 depth triples and verifies the two
// surviving locally source-valid restart suffixes. It does not construct a
// prefix from the blank-tape root.

const branches = {
  A: { t1: 0, T: [0, 14, 5], S: [14, -28, -13], X: [11, -22, -4], nmod: 4, alpha: 9 },
  B: { t1: 0, T: [0, 14, 10], S: [14, -28, -23], X: [11, -22, -12], nmod: 2, alpha: 1 },
  C: { t1: 1, T: [0, 14, 3], S: [14, -28, -11], X: [9, -18, -2], nmod: 2, alpha: 1 }
};

function fail(message) { throw new Error(message); }
function check(condition, message) { if (!condition) fail(message); }
function abs(x) { return x < 0n ? -x : x; }
function gcd(a, b) {
  a = abs(a); b = abs(b);
  while (b !== 0n) { const r = a % b; a = b; b = r; }
  return a;
}
function mod(a, m) { return ((a % m) + m) % m; }
function pow2(k) { return 1n << BigInt(k); }
function powmod(a, n, m) {
  let r = 1n;
  a = mod(a, m);
  while (n > 0n) {
    if ((n & 1n) !== 0n) r = (r * a) % m;
    a = (a * a) % m;
    n >>= 1n;
  }
  return r;
}
function inverse(a, m) {
  let t = 0n, nextT = 1n, r = m, nextR = mod(a, m);
  while (nextR !== 0n) {
    const q = r / nextR;
    const oldT = t, oldR = r;
    t = nextT; nextT = oldT - q * nextT;
    r = nextR; nextR = oldR - q * nextR;
  }
  check(r === 1n, "modular inverse does not exist");
  return mod(t, m);
}
function orderOfTwo(m) {
  let x = 1n;
  for (let i = 1; i <= Number(m) * 2; i++) {
    x = (2n * x) % m;
    if (x === 1n) return i;
  }
  fail("failed to find order of two");
}
function lcm(a, b) { return (a / gcd(a, b)) * b; }

function terminalEquation(branch, r, v, w) {
  const f1 = pow2(r + v + 1);
  const f2 = pow2(r);
  const fR = pow2(r + v + 2 + w);
  const left = [0n, 0n, 0n];
  const right = [0n, 0n, 0n];

  for (let i = 0; i < 3; i++) {
    left[i] =
      f1 * (BigInt(branch.S[i]) + (i === 2 ? 3n - 2n * BigInt(r) - 2n * BigInt(v) : 0n)) +
      f2 * (BigInt(branch.S[i]) + (i === 2 ? 5n - 2n * BigInt(r) : 0n)) +
      BigInt(branch.X[i]);

    right[i] =
      fR * (
        BigInt(branch.S[i]) +
        4n * BigInt(branch.T[i]) +
        (i === 2
          ? 4n * BigInt(branch.t1) + 2n * BigInt(r) + 2n * BigInt(v) + 2n * BigInt(w) + 5n
          : 0n) -
        (i === 0 ? 12n : 0n)
      );
  }

  const raw = left.map((x, i) => x - right[i]);
  const g = gcd(gcd(raw[0], raw[1]), raw[2]);
  let a = raw[0] / g;
  let uCoeff = raw[1] / g;
  let constant = raw[2] / g;
  if (a < 0n) {
    a = -a; uCoeff = -uCoeff; constant = -constant;
  }
  const b = -uCoeff, c = -constant;
  check(a > 0n && b > 0n && c > 0n, "unexpected coefficient sign");
  return { a, b, c };
}

function classifyRow(branch, row) {
  const delta = 98n * row.a - BigInt(branch.alpha) * row.b;
  if (delta > 0n) return { kind: "defect", delta };

  const g = gcd(row.a, row.b);
  if (row.c % g !== 0n) return { kind: "modular", reason: "gcd", delta };

  const a = row.a / g;
  const b = row.b / g;
  const c = row.c / g;
  const twoPart = b & -b;
  const oddPart = b / twoPart;
  if (c % twoPart !== 0n) return { kind: "modular", reason: "2-adic", delta };

  if (oddPart === 1n) return { kind: "survivor", witness: branch.nmod === 4 ? 88 : 86, oddPart, target: 0n, delta };

  const target = mod(c * inverse(a, oddPart), oddPart);
  let x = powmod(2n, 83n, oddPart);
  const end = 83 + 6 * Number(oddPart) + 6;
  for (let n = 83; n < end; n++) {
    if (n % 6 === branch.nmod && x === target) {
      return { kind: "survivor", witness: n, oddPart, target, delta };
    }
    x = (2n * x) % oddPart;
  }
  return { kind: "modular", reason: "complete exponent period", oddPart, target, delta };
}

function sourceStep(state, depth, P, n, label) {
  const power = pow2(depth);
  const X = state.d + state.b / 2n + 3n;
  check(X % power === 0n, label + ": depth divisibility");
  const c = X / power - 3n;
  const numerator = state.b + state.d - c - 2n * BigInt(depth) - 2n;
  check(numerator % 2n === 0n, label + ": k integrality");
  const k = numerator / 2n;
  check(c % 2n === 1n && k % 2n === 0n && k >= 2n, label + ": odd-c/even-k guard");

  const child = {
    b: 2n * k - 4n,
    d: c + 4n,
    B: state.B + BigInt(depth + 1)
  };
  check(child.b >= 8n && child.d >= 1n, label + ": child positivity");
  check(child.b % 4n === 0n && child.d % 2n === 1n, label + ": child congruences");
  check(state.B >= n + 6n, label + ": parent nonnegative cost");
  check(child.B >= n + 6n, label + ": child nonnegative cost");
  check(state.b + state.d + 2n * state.B + 1n === 14n * P, label + ": parent mass");
  check(child.b + child.d + 2n * child.B + 1n === 14n * P, label + ": child mass");
  return child;
}

function verifyLocalFamily(spec) {
  const n = BigInt(spec.n);
  const P = pow2(spec.n);
  const uNumerator = spec.a * P - spec.c;
  check(uNumerator % spec.b === 0n, spec.name + ": u integrality");
  const u = uNumerator / spec.b;
  const M = 14n * u - n - 3n;
  const defectNumerator = 18n * P + 6n - 14n * M;
  check(defectNumerator % 49n === 0n, spec.name + ": D integrality");
  const D = defectNumerator / 49n;
  check(D >= 4n && D % 2n === 0n, spec.name + ": D bound/parity");
  check((n + 2n) % 3n === 0n, spec.name + ": depth-two prefix length");
  const s = Number((n + 2n) / 3n);
  const Bfirst = 14n * u + 5n;
  const first = {
    b: 12n * P - 24n * u - 12n,
    d: 2n * P - 4n * u + 1n,
    B: Bfirst
  };
  check(first.b >= 8n && first.d >= 1n, spec.name + ": first parent positivity");
  check(first.b % 4n === 0n && first.d % 2n === 1n, spec.name + ": first parent congruences");
  check(first.b + first.d + 2n * first.B + 1n === 14n * P, spec.name + ": first parent mass");

  // Reverse the s depth-two edges from the first-shallow parent.
  let child = first;
  for (let j = 0; j < s; j++) {
    const parent = {
      b: 2n * child.b - 6n * child.d + 26n,
      d: 7n * child.d - child.b - 20n,
      B: child.B - 3n
    };
    check(parent.b >= 8n && parent.d >= 1n, spec.name + ": reverse parent positivity at " + j);
    check(parent.b % 4n === 0n && parent.d % 2n === 1n, spec.name + ": reverse parent congruences at " + j);
    check(parent.B >= n + 6n, spec.name + ": reverse parent cost at " + j);
    const next = sourceStep(parent, 2, P, n, spec.name + " reverse depth-two " + j);
    check(next.b === child.b && next.d === child.d && next.B === child.B,
      spec.name + ": reverse/forward mismatch at " + j);
    child = parent;
  }
  const restart = child;
  check(restart.d === D + 1n, spec.name + ": restart d");
  check(restart.B === M + 6n, spec.name + ": restart offset");
  const mRestart = restart.B - n - 6n;
  check(mRestart === 14n * u - 2n * n - 3n && mRestart > 0n, spec.name + ": restart cost");

  // Supply one legal depth-five/depth-seven predecessor of the restart state.
  const V = restart.b + restart.d;
  const deepParent = {
    b: 2n * V + 4n * BigInt(spec.deep) + 10n - pow2(spec.deep + 1) * D,
    d: pow2(spec.deep + 1) * D - V - 2n * BigInt(spec.deep) - 8n,
    B: restart.B - BigInt(spec.deep + 1)
  };
  check(deepParent.b >= 8n && deepParent.d >= 1n, spec.name + ": deep parent positivity");
  check(deepParent.b % 4n === 0n && deepParent.d % 2n === 1n, spec.name + ": deep parent congruences");
  check(deepParent.B >= n + 6n, spec.name + ": deep parent cost");
  const deepChild = sourceStep(deepParent, spec.deep, P, n, spec.name + " deep predecessor");
  check(deepChild.b === restart.b && deepChild.d === restart.d && deepChild.B === restart.B,
    spec.name + ": deep predecessor mismatch");

  // Replay the forward suffix and check the terminal wall exactly.
  let state = restart;
  for (let j = 0; j < s; j++) state = sourceStep(state, 2, P, n, spec.name + " forward depth-two " + j);
  check(state.b === first.b && state.d === first.d && state.B === first.B,
    spec.name + ": forward depth-two prefix mismatch");
  for (let j = 0; j < spec.low.length; j++) {
    state = sourceStep(state, spec.low[j], P, n, spec.name + " low edge " + j);
  }
  const mFinal = state.B - n - 6n;
  check(state.b + 4n * mFinal + 4n * n + 20n === 12n * P, spec.name + ": terminal wall");
  const mParent = deepParent.B - n - 6n;
  check(mParent > n, spec.name + ": synthetic parent must lie beyond n");

  return {
    n: spec.n,
    period: spec.period,
    depthTwoPrefix: s,
    uMod64: String(u % 64n),
    DPositiveEven: true,
    restartCostGreaterThanZero: true,
    syntheticParentCostGreaterThanN: true,
    deepDepth: spec.deep,
    lowDepths: spec.low,
    terminalWall: true
  };
}

const rows = [];
const defectRows = [];
const modularRows = [];
const survivors = [];
for (const name of Object.keys(branches)) {
  const branch = branches[name];
  for (let r = 0; r <= 2; r++) {
    for (let v = 0; v <= 2; v++) {
      for (let w = 0; w <= 2; w++) {
        const equation = terminalEquation(branch, r, v, w);
        const row = { branch: name, r, v, w, a: equation.a, b: equation.b, c: equation.c };
        const classification = classifyRow(branch, equation);
        rows.push(row);
        if (classification.kind === "defect") defectRows.push({ ...row, delta: classification.delta });
        else if (classification.kind === "modular") modularRows.push({ ...row, reason: classification.reason });
        else survivors.push({ ...row, witness: classification.witness, oddPart: classification.oddPart, target: classification.target });
      }
    }
  }
}

check(rows.length === 81, "expected 81 equations");
check(defectRows.length === 56, "expected 56 defect exclusions");
check(modularRows.length === 23, "expected 23 modular exclusions");
check(survivors.length === 2, "expected exactly two survivors");
const maxB = rows.reduce((m, row) => row.b > m ? row.b : m, 0n);
const maxC = rows.reduce((m, row) => row.c > m ? row.c : m, 0n);
const minDelta = defectRows.reduce((m, row) => row.delta < m ? row.delta : m, defectRows[0].delta);
check(maxB === 8198n && maxC === 9700n && minDelta === 160n, "coefficient bounds changed");

const families = [
  { name: "A (0,1,2)", n: 5362, period: 595056, a: 17n, b: 1058n, c: 636n, odd: 529n, target: 193n, deep: 5, low: [0, 0, 1, 2] },
  { name: "A (1,1,1)", n: 9538, period: 703248, a: 87n, b: 1198n, c: 712n, odd: 599n, target: 139n, deep: 7, low: [0, 1, 1, 1] }
];
const familyChecks = [];
for (const family of families) {
  const n = BigInt(family.n);
  const period = BigInt(family.period);
  check(n % 48n === 34n, family.name + ": n mod 48");
  check(period % 48n === 0n && period % 147n === 0n, family.name + ": common period");
  check(period % BigInt(orderOfTwo(family.odd)) === 0n, family.name + ": odd-modulus period");
  check(powmod(2n, n, family.odd) === family.target, family.name + ": terminal odd residue");
  check(mod(18n * powmod(2n, n, 49n) + 14n * n + 48n, 49n) === 0n, family.name + ": D residue");
  const P = pow2(family.n);
  const u = (family.a * P - family.c) / family.b;
  check((family.a * P - family.c) % family.b === 0n, family.name + ": base u");
  check(u % 64n === (family.deep === 5 ? 34n : 4n), family.name + ": low-edge guard residue");
  familyChecks.push(verifyLocalFamily(family));
}

const output = {
  cases: rows.length,
  defectExcluded: defectRows.length,
  modularExcluded: modularRows.length,
  surviving: survivors.length,
  maxB: String(maxB),
  maxC: String(maxC),
  minPositiveDelta: String(minDelta),
  survivors: survivors.map(row => ({
    branch: row.branch,
    depths: [row.r, row.v, row.w],
    equation: String(row.a) + " P = " + String(row.b) + " u + " + String(row.c),
    oddModulus: String(row.oddPart),
    powerResidue: String(row.target),
    witnessExponent: row.witness
  })),
  locallyVerifiedFamilies: familyChecks
};

console.log(JSON.stringify(output, null, 2));
