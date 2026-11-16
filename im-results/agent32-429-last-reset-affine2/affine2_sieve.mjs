#!/usr/bin/env node
// Two-parameter inverse-kernel research prototype for BB(4,2).
//
// Long-burst branches use a 96-bit residue representation. At most two
// precision bits are lost per inverse step; depth 16 therefore leaves 64
// bits, more than the largest terminal modulus (32). Their affine constant
// first coordinate stays >= 13 throughout depth 16 (see README).
//
// Gap branches use exact BigInt arithmetic.
//
// "excluded" means the bounded prototype's terminal-obstruction recursion
// covers every inverse path. This is not a Lean proof until Affine2 soundness
// is formalized.

const ALLOWED8 = new Set([
  "0,0","0,2","1,0","1,1","1,2","2,2","3,1","3,2","3,3",
  "4,2","5,0","5,1","5,2","5,3","6,2","7,2","7,3"
]);
const mod = (x, m) => ((x % m) + m) % m;
const evenN = x => x % 2n === 0n;
const oddN = x => x % 2n === 1n;

// Terminal predicates mirrored from BB429InverseKernelExtended.lean.
function bad(s) {
  const { A1, A2, a, B1, B2, b } = s;
  const ad = m => A1 % BigInt(m) === 0n && A2 % BigInt(m) === 0n;
  const bd = m => B1 % BigInt(m) === 0n && B2 % BigInt(m) === 0n;
  return (
    (ad(8) && bd(4) && !ALLOWED8.has(String(mod(a, 8n)) + "," + String(mod(b, 4n)))) ||
    (ad(2) && bd(8) && s.large && evenN(a) && mod(b, 8n) !== 2n) ||
    (ad(8) && bd(8) && mod(a, 8n) === 7n && mod(b, 8n) === 7n) ||
    (ad(16) && bd(8) && mod(a, 16n) === 1n && mod(b, 8n) === 6n) ||
    (ad(16) && bd(8) && mod(a, 16n) === 5n && mod(b, 8n) === 6n) ||
    (ad(32) && bd(16) && mod(a, 32n) === 5n && mod(b, 16n) === 1n) ||
    (ad(16) && bd(8) && mod(a, 16n) === 11n && ![2n, 6n, 7n].includes(mod(b, 8n))) ||
    (ad(32) && bd(8) && [19n, 27n].includes(mod(a, 32n)) && ![2n, 7n].includes(mod(b, 8n)))
  );
}

function oddFamily(s) {
  return s.large && oddN(s.a) &&
    evenN(s.A1) && evenN(s.A2) &&
    s.B1 % 4n === 0n && s.B2 % 4n === 0n;
}
function evenFamily(s) {
  return s.large && evenN(s.a) &&
    evenN(s.A1) && evenN(s.A2) &&
    s.B1 % 4n === 0n && s.B2 % 4n === 0n;
}

// Exact BigInt F/S/E kernel, used for branches 5 and 6.
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
function certExact(depth, s, memo = new Map()) {
  const key = [depth, s.A1, s.A2, s.a, s.B1, s.B2, s.b].join(",");
  if (memo.has(key)) return memo.get(key);
  if (depth === 0) {
    const answer = bad({ ...s, large: s.a >= 1n });
    memo.set(key, answer);
    return answer;
  }
  if (bad({ ...s, large: s.a >= 1n })) {
    memo.set(key, true);
    return true;
  }
  let answer = false;
  const large = s.a >= 13n;
  if (large && oddN(s.a) && evenN(s.A1) && evenN(s.A2) &&
      s.B1 % 4n === 0n && s.B2 % 4n === 0n) {
    answer = certExact(depth - 1, F(s), memo) &&
      (mod(s.b, 4n) === 2n ? certExact(depth - 1, S(s), memo) : true);
  } else if (large && evenN(s.a) && evenN(s.A1) && evenN(s.A2) &&
      s.B1 % 4n === 0n && s.B2 % 4n === 0n) {
    answer = mod(s.b, 4n) === 2n ? certExact(depth - 1, E(s), memo) : false;
  }
  memo.set(key, answer);
  return answer;
}

// Modular version for long-burst families. The "large" flag is justified
// uniformly: the smallest initial constant is branch 1 at t=4,
// 24*256^4-22 > 2^36. Across 16 inverse steps the first coordinate remains
// >13 (F is the worst reduction; S/E reduce it by less than a factor 2).
function certLongMod(branch, t, splitBits, depth) {
  const precision = 96;
  const modulus = 1n << BigInt(precision);
  const K = BigInt(branch === 1 || branch === 7 ? 24 : branch === 2 ? 28 : 6);
  const C = t >= 12 ? 0n : (K * (256n ** BigInt(t))) % modulus;
  const h = BigInt(branch === 1 || branch === 2 ? 10 : branch === 3 ? 7 : 6);
  const c = BigInt(branch === 1 ? 2 : branch === 2 ? 1 : branch === 3 ? 0 : branch === 4 ? -2 : -3);
  const A2 = mod(C - 3n * (2n ** BigInt(splitBits)), modulus);
  const a = mod(C - 3n * BigInt(t) - h, modulus);
  const b = mod(2n * a + c, modulus);
  const root = {
    bits: precision, A1: C, A2, a,
    B1: mod(2n * C, modulus), B2: mod(2n * A2, modulus), b,
    large: true
  };
  const memo = new Map();
  const trim = (x, bits) => mod(x, 1n << BigInt(bits));
  function f(s) {
    const bits = s.bits - 1, old = 1n << BigInt(s.bits), mask = (1n << BigInt(bits)) - 1n;
    const div2 = x => mod(x, old) / 2n;
    return {
      bits, A1: div2(s.A1) & mask, A2: div2(s.A2) & mask,
      a: mod(s.a - 3n, old) / 2n & mask,
      B1: trim(s.B1 + s.A1, bits), B2: trim(s.B2 + s.A2, bits),
      b: trim(s.b + s.a, bits), large: true
    };
  }
  function sParent(s) {
    const bits = s.bits - 2, old = 1n << BigInt(s.bits), mask = (1n << BigInt(bits)) - 1n;
    const div4 = x => mod(x, old) / 4n, div2 = x => mod(x, old) / 2n;
    return {
      bits, A1: trim(s.A1 + div4(s.B1), bits), A2: trim(s.A2 + div4(s.B2), bits),
      a: mod(4n * s.a + s.b - 26n, old) / 4n & mask,
      B1: div2(s.B1) & mask, B2: div2(s.B2) & mask,
      b: mod(s.b + 4n, old) / 2n & mask, large: true
    };
  }
  function eParent(s) {
    const bits = s.bits - 2, old = 1n << BigInt(s.bits), mask = (1n << BigInt(bits)) - 1n;
    const div4 = x => mod(x, old) / 4n, div2 = x => mod(x, old) / 2n;
    return {
      bits, A1: trim(s.A1 + div4(s.B1), bits), A2: trim(s.A2 + div4(s.B2), bits),
      a: mod(4n * s.a + s.b - 14n, old) / 4n & mask,
      B1: div2(s.B1) & mask, B2: div2(s.B2) & mask,
      b: div2(s.b) & mask, large: true
    };
  }
  function rec(d, s) {
    const key = [d, s.bits, s.A1, s.A2, s.a, s.B1, s.B2, s.b].join(",");
    if (memo.has(key)) return memo.get(key);
    if (d === 0 || bad(s)) {
      const answer = bad(s);
      memo.set(key, answer);
      return answer;
    }
    let answer = false;
    if (oddFamily(s)) {
      answer = rec(d - 1, f(s)) &&
        (mod(s.b, 4n) === 2n ? rec(d - 1, sParent(s)) : true);
    } else if (evenFamily(s)) {
      answer = mod(s.b, 4n) === 2n ? rec(d - 1, eParent(s)) : false;
    }
    memo.set(key, answer);
    return answer;
  }
  return { excluded: rec(depth, root), visitedStates: memo.size };
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

function runLongBranchesStaged(firstBits, firstDepth, childBits, childDepth) {
  const M = 2 ** firstBits;
  const specs = [
    { branch: 1, tMin: 4 },
    { branch: 2, tMin: 5 },
    { branch: 3, tMin: 5 },
    { branch: 4, tMin: 5 },
    { branch: 7, tMin: 4 }
  ];
  return specs.map(({ branch, tMin }) => {
    const firstUnresolved = [];
    let firstVisited = 0;
    for (let r = 0; r < M; r++) {
      const z = certLongMod(branch, tMin + r, firstBits, firstDepth);
      firstVisited += z.visitedStates;
      if (!z.excluded) firstUnresolved.push(r);
    }
    const childUnresolved = [];
    let childVisited = 0;
    for (const r of firstUnresolved) {
      for (let j = 0; j < 4; j++) {
        const childOffset = r + j * M;
        const z = certLongMod(branch, tMin + childOffset, childBits, childDepth);
        childVisited += z.visitedStates;
        if (!z.excluded) childUnresolved.push(childOffset);
      }
    }
    return {
      branch, firstBits, firstDepth, firstFamilies: M,
      firstExcluded: M - firstUnresolved.length,
      firstUnresolved: firstUnresolved.length,
      firstUnresolvedOffsets: firstUnresolved,
      childBits, childDepth, childFamilies: firstUnresolved.length * 4,
      childExcluded: firstUnresolved.length * 4 - childUnresolved.length,
      childUnresolved: childUnresolved.length,
      childUnresolvedOffsets: childUnresolved,
      firstMeanVisitedStates: firstVisited / M,
      childMeanVisitedStates: firstUnresolved.length ? childVisited / (firstUnresolved.length * 4) : 0
    };
  });
}

function powMod(base, exponent, modulus) {
  let a = mod(base, modulus), e = exponent, result = 1n;
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

function runGapBranches(splitBits, depth) {
  const M = 2 ** splitBits;
  const specs = [{ branch: 5, tMin: 5 }, { branch: 6, tMin: 5 }];
  return specs.map(({ branch, tMin }) => {
    let excluded = 0;
    const unresolved = [];
    let totalNodes = 0;
    for (let rt = 0; rt < M; rt++) {
      const t = tMin + rt;
      for (let e0 = 1; e0 <= M; e0++) {
        const memo = new Map();
        const ok = certExact(depth, gapFamily(branch, t, e0, splitBits), memo);
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

const result = {
  longFirstBits: Number(process.env.LONG_BITS || 14),
  longFirstDepth: Number(process.env.LONG_DEPTH || 14),
  longChildBits: Number(process.env.LONG_CHILD_BITS || 16),
  longChildDepth: Number(process.env.LONG_CHILD_DEPTH || 16),
  gapBits: Number(process.env.GAP_BITS || 9),
  gapDepth: Number(process.env.GAP_DEPTH || 14)
};
result.longBurstBranches = runLongBranchesStaged(
  result.longFirstBits, result.longFirstDepth, result.longChildBits, result.longChildDepth
);
result.gapBranches = runGapBranches(result.gapBits, result.gapDepth);
console.log(JSON.stringify(result, null, 2));
