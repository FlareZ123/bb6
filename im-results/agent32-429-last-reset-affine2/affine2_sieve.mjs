#!/usr/bin/env node
// Exact BigInt research prototype for the two-parameter inverse sieve.
// "true" from cert means the whole affine family is excluded by the
// terminal root invariants within the requested inverse depth. A false
// result is only unresolved, never evidence of reachability.

const ALLOWED8 = new Set([
  "0,0","0,2","1,0","1,1","1,2","2,2","3,1","3,2","3,3",
  "4,2","5,0","5,1","5,2","5,3","6,2","7,2","7,3"
]);

const mod = (x, m) => ((x % m) + m) % m;
const evenN = x => x % 2n === 0n;
const oddN = x => x % 2n === 1n;

function bad(s) {
  const { A1, A2, a, B1, B2, b } = s;
  const ad = m => A1 % BigInt(m) === 0n && A2 % BigInt(m) === 0n;
  const bd = m => B1 % BigInt(m) === 0n && B2 % BigInt(m) === 0n;
  return (
    (ad(8) && bd(4) && !ALLOWED8.has(String(mod(a, 8n)) + "," + String(mod(b, 4n)))) ||
    (ad(2) && bd(8) && a > 0n && evenN(a) && mod(b, 8n) !== 2n) ||
    (ad(8) && bd(8) && mod(a, 8n) === 7n && mod(b, 8n) === 7n) ||
    (ad(16) && bd(8) && mod(a, 16n) === 1n && mod(b, 8n) === 6n) ||
    (ad(16) && bd(8) && mod(a, 16n) === 5n && mod(b, 8n) === 6n) ||
    (ad(32) && bd(16) && mod(a, 32n) === 5n && mod(b, 16n) === 1n) ||
    (ad(16) && bd(8) && mod(a, 16n) === 11n && ![2n, 6n, 7n].includes(mod(b, 8n))) ||
    (ad(32) && bd(8) && [19n, 27n].includes(mod(a, 32n)) && ![2n, 7n].includes(mod(b, 8n)))
  );
}

function oddFamily(s) {
  return s.a >= 13n && oddN(s.a) &&
    evenN(s.A1) && evenN(s.A2) &&
    s.B1 % 4n === 0n && s.B2 % 4n === 0n;
}

function evenFamily(s) {
  return s.a >= 6n && evenN(s.a) &&
    evenN(s.A1) && evenN(s.A2) &&
    s.B1 % 4n === 0n && s.B2 % 4n === 0n;
}

// Inverse parents for a target (u,w):
// F: ((u-3)/2, w+u)
// S: ((4u+w-26)/4, (w+4)/2)
// E: ((4u+w-14)/4, w/2)
function F(s) {
  return {
    A1: s.A1 / 2n, A2: s.A2 / 2n, a: (s.a - 3n) / 2n,
    B1: s.B1 + s.A1, B2: s.B2 + s.A2, b: s.b + s.a
  };
}
function S(s) {
  return {
    A1: s.A1 + s.B1 / 4n, A2: s.A2 + s.B2 / 4n,
    a: (4n * s.a + s.b - 26n) / 4n,
    B1: s.B1 / 2n, B2: s.B2 / 2n, b: (s.b + 4n) / 2n
  };
}
function E(s) {
  return {
    A1: s.A1 + s.B1 / 4n, A2: s.A2 + s.B2 / 4n,
    a: (4n * s.a + s.b - 14n) / 4n,
    B1: s.B1 / 2n, B2: s.B2 / 2n, b: s.b / 2n
  };
}

// Mirrors the depth-bounded certificate recursion in
// im-results/agent1-429-root-rows/BB429InverseKernelExtended.lean,
// generalized experimentally from one affine parameter to two.
function cert(depth, s, memo = new Map()) {
  const key = [depth, s.A1, s.A2, s.a, s.B1, s.B2, s.b].join(",");
  if (memo.has(key)) return memo.get(key);
  if (depth === 0) {
    const answer = bad(s);
    memo.set(key, answer);
    return answer;
  }
  if (bad(s)) {
    memo.set(key, true);
    return true;
  }

  let answer = false;
  if (oddFamily(s)) {
    answer = cert(depth - 1, F(s), memo) &&
      (mod(s.b, 4n) === 2n ? cert(depth - 1, S(s), memo) : true);
  } else if (evenFamily(s)) {
    answer = mod(s.b, 4n) === 2n ? cert(depth - 1, E(s), memo) : false;
  }
  memo.set(key, answer);
  return answer;
}

function longBurstFamily(branch, t, splitBits) {
  const C0 = branch === 1 || branch === 7 ? 24n : branch === 2 ? 28n : 6n;
  const xOffset = branch === 1 || branch === 2 ? 10n : branch === 3 ? 7n : 6n;
  const yShift = branch === 1 ? 2n : branch === 2 ? 1n :
    branch === 3 ? 0n : branch === 4 ? -2n : -3n;
  const C = C0 * (256n ** BigInt(t));
  const A2 = C - 3n * (2n ** BigInt(splitBits));
  const a = C - 3n * BigInt(t) - xOffset;
  return { A1: C, A2, a, B1: 2n * C, B2: 2n * A2, b: 2n * a + yShift };
}

function powMod(base, exponent, modulus) {
  let a = mod(base, modulus);
  let e = exponent;
  let result = 1n;
  while (e > 0n) {
    if (e % 2n === 1n) result = (result * a) % modulus;
    a = (a * a) % modulus;
    e /= 2n;
  }
  return result;
}

function gapFamily(branch, t, e0, splitBits) {
  const M = 2n ** BigInt(splitBits);
  const coefficient = branch === 5 ? 28n : 6n;
  const gapOffset = branch === 5 ? 9n : 7n;
  const delta = branch === 5 ? 0n : 1n;
  const powerResidue = powMod(256n, BigInt(t), M);
  const r0 = mod(coefficient * powerResidue - 3n * BigInt(t) - gapOffset - BigInt(e0), M);
  return {
    A1: M, A2: 2n * M, a: r0 + 2n * BigInt(e0) + delta,
    B1: 2n * M, B2: 0n, b: 2n * r0
  };
}

function runLongBranches(splitBits, depth) {
  const M = 2 ** splitBits;
  const specs = [
    { branch: 1, tMin: 4 },
    { branch: 2, tMin: 5 },
    { branch: 3, tMin: 5 },
    { branch: 4, tMin: 5 },
    { branch: 7, tMin: 4 }
  ];
  return specs.map(({ branch, tMin }) => {
    let excluded = 0;
    const unresolved = [];
    let totalNodes = 0;
    for (let r = 0; r < M; r++) {
      const t = tMin + r;
      const memo = new Map();
      const ok = cert(depth, longBurstFamily(branch, t, splitBits), memo);
      totalNodes += memo.size;
      if (ok) excluded++;
      else unresolved.push(r);
    }
    return {
      branch, splitBits, families: M, excluded, unresolved: unresolved.length,
      unresolvedOffsets: unresolved, meanVisitedStates: totalNodes / M
    };
  });
}

function runGapBranches(splitBits, depth) {
  const M = 2 ** splitBits;
  const specs = [
    { branch: 5, tMin: 5 },
    { branch: 6, tMin: 5 }
  ];
  return specs.map(({ branch, tMin }) => {
    let excluded = 0;
    const unresolved = [];
    let totalNodes = 0;
    for (let rt = 0; rt < M; rt++) {
      const t = tMin + rt;
      for (let e0 = 1; e0 <= M; e0++) {
        const memo = new Map();
        const ok = cert(depth, gapFamily(branch, t, e0, splitBits), memo);
        totalNodes += memo.size;
        if (ok) excluded++;
        else unresolved.push([rt, e0]);
      }
    }
    return {
      branch, splitBits, families: M * M, excluded, unresolved: unresolved.length,
      unresolvedPairs: unresolved, meanVisitedStates: totalNodes / (M * M)
    };
  });
}

const depth = Number(process.env.DEPTH || 14);
const longBits = Number(process.env.LONG_BITS || 12);
const gapBits = Number(process.env.GAP_BITS || 9);
const result = {
  depth,
  longBits,
  gapBits,
  longBurstBranches: runLongBranches(longBits, depth),
  gapBranches: runGapBranches(gapBits, depth)
};
console.log(JSON.stringify(result, null, 2));
