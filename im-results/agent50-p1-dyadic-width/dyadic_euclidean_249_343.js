"use strict";

// Exact BigInt analysis of the P1 reverse-parent map near the two
// fourth-edge restart families. The 249/343 orbit is an ideal reference
// orbit; this script does not claim it is an exact source orbit.

function check(ok, message) { if (!ok) throw new Error(message); }
function bitlen(x) { return x.toString(2).length; }
function pow2(k) { return 1n << BigInt(k); }
function mod(a, m) { return ((a % m) + m) % m; }

const families = [
  {
    name: "Case I",
    n: 5362,
    a: 17n, b: 1058n, c: 636n,
    prefix: [6, 2]
  },
  {
    name: "Case II",
    n: 9538,
    a: 87n, b: 1198n, c: 712n,
    prefix: [8, 1, 2, 3, 3, 1, 1, 1, 4, 1, 1, 2, 4]
  }
];

function idealPeriod() {
  let p = 249n;
  const word = [];
  let total = 0;
  for (let i = 0; i < 73; i++) {
    let k = 1;
    while (pow2(k) * p < 343n) k++;
    word.push(k);
    total += k;
    p = pow2(k) * p - 343n;
  }
  check(p === 249n, "ideal numerator did not return after 73 symbols");
  check(total === 147, "ideal word does not consume 147 bits");
  return word;
}

function applyIdealWord(numerator, word) {
  let p = BigInt(numerator);
  for (const k of word) p = pow2(k) * p - 21952n;
  return p;
}

function symbolicError(family) {
  // D_R and N_R are represented over common denominator 49*b.
  const den = 49n * family.b;
  let dP = 18n * family.b - 196n * family.a;
  let dn = 14n * family.b;
  let d0 = 48n * family.b + 196n * family.c;

  let nP = 49n * (14n * family.b - 28n * family.a);
  let nn = 98n * family.b;
  let n0 = 49n * (28n * family.c - family.b);

  for (const k0 of family.prefix) {
    const q = pow2(k0);
    dP = q * dP - nP;
    dn = q * dn - nn;
    d0 = q * d0 - n0 - den * (2n * BigInt(k0) + 1n);
    n0 += 2n * BigInt(k0) * den;
  }

  const eP = 343n * dP - 249n * nP;
  const en = 343n * dn - 249n * nn;
  const e0 = 343n * d0 - 249n * n0;
  check(eP === 0n, family.name + ": leading P coefficient did not cancel");
  check(en % den === 0n && e0 % den === 0n, family.name + ": error formula not integral");
  return { nCoefficient: en / den, constant: e0 / den };
}

function cycleAffineMap(word) {
  let A = 1n, B = 0n, C = 0n;
  for (const k0 of word) {
    const q = pow2(k0);
    A = q * A;
    B = q * B - 1n;
    C = q * C - 2n * BigInt(k0) - 1n;
  }
  check(A === pow2(147), "cycle multiplier is not 2^147");
  check(B === -249n * (A - 1n) / 343n, "cycle linear coefficient mismatch");
  const epsilonConstant = 343n * C - 249n * 294n;
  check(epsilonConstant === -149561324732188410108221871335825455518140815349n,
    "cycle epsilon constant mismatch");
  return { A, B, C, epsilonConstant };
}

function parentCandidates(D, N, m) {
  const k0 = bitlen(N) - bitlen(D);
  const candidates = [];
  for (let k = Math.max(1, k0 - 4); k <= k0 + 4; k++) {
    const K = BigInt(k);
    if (K > m) continue;
    const Np = N + 2n * K;
    const scaled = pow2(k) * D;
    if (scaled < Np + 1n || scaled > 2n * Np - 14n) continue;
    const Dp = scaled - Np - 1n;
    const mp = m - K;
    const bp = 2n * Np - scaled - 6n;
    const dp = Dp + 1n;
    check(bp >= 8n && bp % 4n === 0n, "parent left-coordinate guard");
    check(dp >= 1n && dp % 2n === 1n, "parent right-coordinate guard");
    candidates.push({ k, D: Dp, N: Np, m: mp });
  }
  return candidates;
}

function initialState(family) {
  const n = BigInt(family.n);
  const P = pow2(family.n);
  const uNumerator = family.a * P - family.c;
  check(uNumerator % family.b === 0n, family.name + ": u integrality");
  const u = uNumerator / family.b;
  const M = 14n * u - n - 3n;
  const defectNumerator = 18n * P + 6n - 14n * M;
  check(defectNumerator % 49n === 0n, family.name + ": defect integrality");
  const D = defectNumerator / 49n;
  const N = 14n * P - 28n * u + 2n * n - 1n;
  const m = 14n * u - 2n * n - 3n;
  check(N % 2n === 1n && D % 2n === 0n, family.name + ": parity");
  check(14n * P - 2n * n - 7n - N === 2n * m, family.name + ": root/restart cost relation");
  return { D, N, m };
}

function shadowFamily(family, word, maxSteps) {
  let state = initialState(family);
  for (const expectedK of family.prefix) {
    const candidates = parentCandidates(state.D, state.N, state.m);
    check(candidates.length === 1, family.name + ": initial reverse parent not unique");
    check(candidates[0].k === expectedK, family.name + ": initial reverse word mismatch");
    state = candidates[0];
  }

  const initialError = 343n * state.D - 249n * state.N;
  const symbolic = symbolicError(family);
  const expectedError = symbolic.nCoefficient * BigInt(family.n) + symbolic.constant;
  check(initialError === expectedError, family.name + ": symbolic error mismatch");

  let consumed = 0n;
  for (let i = 0; i < maxSteps; i++) {
    const candidates = parentCandidates(state.D, state.N, state.m);
    check(candidates.length === 1, family.name + ": reverse parent ceased to be unique");
    const actualK = candidates[0].k;
    const idealK = word[i % word.length];
    if (actualK !== idealK) {
      const phase = Number(consumed % 147n);
      const phaseNumerator = mod(249n * pow2(phase), 343n);
      return {
        initialWord: family.prefix,
        initialError: String(initialError),
        errorFormula: String(symbolic.nCoefficient) + " n + " + String(symbolic.constant),
        commonCycleSymbols: i,
        commonCycleCost: String(consumed),
        firstActualK: actualK,
        firstIdealK: idealK,
        idealPhaseNumerator: String(phaseNumerator),
        stateDbits: bitlen(state.D),
        stateNbits: bitlen(state.N)
      };
    }
    consumed += BigInt(actualK);
    state = candidates[0];
  }
  throw new Error(family.name + ": no mismatch within configured bound");
}

const word = idealPeriod();
const affine = cycleAffineMap(word);
check(applyIdealWord(491n, [6, 2]) === 15936n, "Case I limit prefix mismatch");
check(applyIdealWord(141n, [8, 1, 2, 3, 3, 1, 1, 1, 4, 1, 1, 2, 4]) === 15936n,
  "Case II limit prefix mismatch");
check(15936n === 64n * 249n, "common limit ratio mismatch");

const output = {
  idealWordLength: word.length,
  idealBitPeriod: 147,
  idealWordCost: word.reduce((a, b) => a + b, 0),
  idealWord: word,
  commonLimit: "249/343",
  cycleEpsilonConstant: String(affine.epsilonConstant),
  cycleEpsilonFixedPoint: "149561324732188410108221871335825455518140815349/(2^147-1)",
  baseShadowing: families.map(f => shadowFamily(f, word, 10000))
};

console.log(JSON.stringify(output, null, 2));
