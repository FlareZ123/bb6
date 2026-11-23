"use strict";

// Fast-forward exact reverse-parent chains through the 249/343 reference
// word. Every phase inequality is checked; only a complete valid 73-symbol
// block is advanced with the exact affine block map.

function check(ok, message) { if (!ok) throw new Error(message); }
function bitlen(x) { return x.toString(2).length; }
function pow2(k) { return 1n << BigInt(k); }

const families = [
  { name: "Case I base", n: 5362, a: 17n, b: 1058n, c: 636n,
    prefix: [6, 2] },
  { name: "Case I next progression member", n: 600418, a: 17n, b: 1058n, c: 636n,
    prefix: [6, 2] },
  { name: "Case II base", n: 9538, a: 87n, b: 1198n, c: 712n,
    prefix: [8, 1, 2, 3, 3, 1, 1, 1, 4, 1, 1, 2, 4] },
  { name: "Case II next progression member", n: 712786, a: 87n, b: 1198n, c: 712n,
    prefix: [8, 1, 2, 3, 3, 1, 1, 1, 4, 1, 1, 2, 4] }
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
  check(p === 249n && total === 147, "bad 249/343 period");
  return word;
}

function prefixMaps(word) {
  let A = 1n, B = 0n, C = 0n, K = 0n, p = 249n;
  const maps = [];
  for (const k0 of word) {
    const k = BigInt(k0), q = pow2(k0), Knext = K + k;
    maps.push({ A, B, C, K, k: k0, p });
    A = q * A;
    B = q * B - 1n;
    C = q * C - 2n * Knext - 1n;
    K = Knext;
    p = q * p - 343n;
  }
  return maps;
}

function parentCandidates(D, N, m) {
  const k0 = bitlen(N) - bitlen(D);
  const out = [];
  for (let k = Math.max(1, k0 - 4); k <= k0 + 4; k++) {
    const K = BigInt(k);
    if (K > m) continue;
    const Np = N + 2n * K;
    const scaled = pow2(k) * D;
    if (scaled < Np + 1n || scaled > 2n * Np - 14n) continue;
    const Dp = scaled - Np - 1n;
    const bp = 2n * Np - scaled - 6n;
    const dp = Dp + 1n;
    check(bp >= 8n && bp % 4n === 0n, "parent b guard");
    check(dp >= 1n && dp % 2n === 1n, "parent d guard");
    out.push({ k, D: Dp, N: Np, m: m - K });
  }
  return out;
}

function initialState(family) {
  const n = BigInt(family.n), P = pow2(family.n);
  const un = family.a * P - family.c;
  check(un % family.b === 0n, family.name + ": u integrality");
  const u = un / family.b;
  const M = 14n * u - n - 3n;
  const dn = 18n * P + 6n - 14n * M;
  check(dn % 49n === 0n, family.name + ": defect integrality");
  const D = dn / 49n;
  const N = 14n * P - 28n * u + 2n * n - 1n;
  const m = 14n * u - 2n * n - 3n;
  check(D % 2n === 0n && N % 2n === 1n, family.name + ": parity");
  check(14n * P - 2n * n - 7n - N === 2n * m, family.name + ": root cost");
  let state = { D, N, m };
  for (const expected of family.prefix) {
    const candidates = parentCandidates(state.D, state.N, state.m);
    check(candidates.length === 1 && candidates[0].k === expected,
      family.name + ": initial word mismatch");
    state = candidates[0];
  }
  return state;
}

function cycleAffine(word) {
  let A = 1n, B = 0n, C = 0n;
  for (const k0 of word) {
    const q = pow2(k0);
    A = q * A;
    B = q * B - 1n;
    C = q * C - 2n * BigInt(k0) - 1n;
  }
  check(A === pow2(147), "cycle A coefficient");
  check(B === -249n * (A - 1n) / 343n, "cycle B coefficient");
  const epsilonConstant = 343n * C - 249n * 294n;
  check(epsilonConstant === -149561324732188410108221871335825455518140815349n,
    "cycle epsilon constant");
  return { A, B, C, epsilonConstant };
}

function shadowByBlocks(family, word, maps, affine, maxCycles = 10000) {
  let state = initialState(family);
  let epsilon = 343n * state.D - 249n * state.N;
  let cycles = 0;

  for (; cycles < maxCycles; cycles++) {
    for (let j = 0; j < 73; j++) {
      const phase = maps[j];
      const Dj = phase.A * state.D + phase.B * state.N + phase.C;
      const Nj = state.N + 2n * phase.K;
      const Nnext = Nj + 2n * BigInt(phase.k);
      const scaled = pow2(phase.k) * Dj;

      if (scaled < Nnext + 1n || scaled > 2n * Nnext - 14n) {
        const candidates = parentCandidates(Dj, Nj, state.m - phase.K);
        check(candidates.length === 1, family.name + ": expected unique actual parent");
        const cost = 147n * BigInt(cycles) + phase.K;
        return {
          name: family.name,
          fullCycles: cycles,
          steps: 73 * cycles + j,
          consumedCost: String(cost),
          phaseNumerator: String(phase.p),
          idealNextK: phase.k,
          actualNextK: candidates[0].k,
          epsilonBits: bitlen(epsilon),
          Nbits: bitlen(state.N)
        };
      }
    }

    // All 73 phase inequalities hold, so the exact cycle block is valid.
    epsilon = pow2(147) * epsilon + affine.epsilonConstant;
    state.N += 294n;
    const numerator = 249n * state.N + epsilon;
    check(numerator % 343n === 0n, family.name + ": cycle D divisibility");
    state.D = numerator / 343n;
    state.m -= 147n;
  }
  throw new Error(family.name + ": no mismatch within cycle bound");
}

const word = idealPeriod();
const maps = prefixMaps(word);
const affine = cycleAffine(word);
const results = families.map(f => shadowByBlocks(f, word, maps, affine));
console.log(JSON.stringify({
  idealWordLength: word.length,
  idealBitCost: word.reduce((a, b) => a + b, 0),
  idealWord: word,
  epsilonCycleMultiplier: "2^147",
  epsilonCycleConstant: String(affine.epsilonConstant),
  results
}, null, 2));
