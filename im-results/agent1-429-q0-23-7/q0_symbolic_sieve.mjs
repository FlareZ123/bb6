#!/usr/bin/env node
"use strict";

// Exact q0 inverse residue sieve for u >= 1, depth 12.
// No dependencies; requires Node.js with BigInt support.

const DEPTH = 12;
const MOD_BITS = 12;
const MODULUS = 1 << MOD_BITS;
const pow2 = (n) => 1n << BigInt(n);
const mod = (x, m) => ((x % m) + m) % m;

function v2(x) {
  if (x === 0n) return Infinity;
  let n = 0;
  while ((x & 1n) === 0n) {
    x >>= 1n;
    n++;
  }
  return n;
}

function allowed(a8, b8) {
  const w = b8 % 4;
  switch (a8 % 8) {
    case 0: return w === 0 || w === 2;
    case 1: return w === 0 || w === 1 || w === 2;
    case 2: return w === 2;
    case 3: return w === 1 || w === 2 || w === 3;
    case 4: return w === 2;
    case 5: return true;
    case 6: return w === 2;
    case 7: return w === 2 || w === 3;
    default: throw new Error("unreachable residue");
  }
}

function rootCompatible(a8, b8) {
  return allowed(a8, b8) && (a8 % 2 === 1 || b8 === 2);
}

// A state is:
//   a(u) = (A*u + B) / 2^d
//   b(u) = (C*u + D) / 2^d
// valid on u = r (mod 2^m).
// The omitted 13*2^n and 26*2^n terms vanish mod 8 for u>=1,
// because n>=55 and d<=2*DEPTH=24.

function symbolicSieve() {
  const stack = [{
    r: 0n, m: 0, d: 0,
    A: -24n, B: -19n,
    C: -48n, D: -51n,
    steps: 0
  }];
  const open = new Map();
  let processed = 0;
  let splitNodes = 0;
  let deadPaths = 0;
  let openPaths = 0;

  while (stack.length > 0) {
    const s = stack.pop();
    processed++;

    // Need both coordinates modulo 8 to be constant on this u-cylinder.
    const needA = s.A === 0n ? 0 : s.d + 3 - v2(s.A);
    const needB = s.C === 0n ? 0 : s.d + 3 - v2(s.C);
    const need = Math.max(0, needA, needB);

    if (s.m < need) {
      const nextM = s.m + 1;
      stack.push({ ...s, r: s.r, m: nextM });
      stack.push({ ...s, r: s.r + pow2(s.m), m: nextM });
      splitNodes++;
      continue;
    }

    const den = pow2(s.d);
    const modulus = pow2(s.d + 3);
    const numA = mod(s.A * s.r + s.B, modulus);
    const numB = mod(s.C * s.r + s.D, modulus);

    // Integrality follows inductively from the selected F/S/E branch.
    if (numA % den !== 0n || numB % den !== 0n) {
      throw new Error("non-integral affine state; branch invariant bug");
    }

    const a8 = Number(numA / den);
    const b8 = Number(numB / den);
    const even = a8 % 2 === 0;

    if (!rootCompatible(a8, b8)) {
      deadPaths++;
      continue;
    }

    if (s.steps === DEPTH) {
      if (s.m !== MOD_BITS) {
        throw new Error("open leaf did not refine to modulus 2^12");
      }
      const residue = Number(s.r);
      const key = String(residue);
      if (!open.has(key)) open.set(key, []);
      open.get(key).push({ pathLength: s.steps, a8, b8 });
      openPaths++;
      continue;
    }

    const d = s.d;
    if (!even) {
      // F: ((a-3)/2, b+a), denominator exponent d+1.
      stack.push({
        r: s.r, m: s.m, d: d + 1,
        A: s.A,
        B: s.B - 3n * pow2(d),
        C: 2n * (s.C + s.A),
        D: 2n * (s.D + s.B),
        steps: s.steps + 1
      });

      // S: ((4a+b-26)/4, (b+4)/2), when b = 2 (mod 4).
      if (b8 % 4 === 2) {
        stack.push({
          r: s.r, m: s.m, d: d + 2,
          A: 4n * s.A + s.C,
          B: 4n * s.B + s.D - 26n * pow2(d),
          C: 2n * s.C,
          D: 2n * s.D + 8n * pow2(d),
          steps: s.steps + 1
        });
      }
    } else {
      // A root-compatible positive-even state has b = 2 (mod 8),
      // so E is its only possible inverse.
      stack.push({
        r: s.r, m: s.m, d: d + 2,
        A: 4n * s.A + s.C,
        B: 4n * s.B + s.D - 14n * pow2(d),
        C: 2n * s.C,
        D: 2n * s.D,
        steps: s.steps + 1
      });
    }
  }

  const residues = [...open.keys()].map(Number).sort((a, b) => a - b);
  return {
    processed,
    splitNodes,
    deadPaths,
    openPaths,
    openResidues: residues,
    openResidueCount: residues.length
  };
}

function directRepresentative(u) {
  const n = 23 + 32 * u;
  const a0 = 13n * (1n << BigInt(n)) - 24n * BigInt(u) - 19n;
  const b0 = 2n * a0 - 13n;
  let states = [[a0, b0]];

  for (let step = 0; step < DEPTH; step++) {
    const next = [];
    for (const [a, b] of states) {
      if ((a & 1n) === 1n && a >= 13n) {
        const af = (a - 3n) / 2n;
        const bf = b + a;
        if (af > 0n && allowed(Number(mod(af, 8n)), Number(mod(bf, 8n))) &&
            !((af & 1n) === 0n && mod(bf, 8n) !== 2n)) {
          next.push([af, bf]);
        }

        if (mod(b, 4n) === 2n) {
          const as = (4n * a + b - 26n) / 4n;
          const bs = (b + 4n) / 2n;
          if (as > 0n && allowed(Number(mod(as, 8n)), Number(mod(bs, 8n))) &&
              !((as & 1n) === 0n && mod(bs, 8n) !== 2n)) {
            next.push([as, bs]);
          }
        }
      } else if ((a & 1n) === 0n && a >= 6n && mod(b, 4n) === 2n) {
        const ae = (4n * a + b - 14n) / 4n;
        const be = b / 2n;
        if (ae > 0n && allowed(Number(mod(ae, 8n)), Number(mod(be, 8n))) &&
            mod(be, 8n) === 2n) {
          next.push([ae, be]);
        }
      }
    }
    states = next;
    if (states.length === 0) return false;
  }
  return states.length > 0;
}

function main() {
  const result = symbolicSieve();
  const open = new Set(result.openResidues);

  // Exhaustively compare one exact representative of each u (mod 4096)
  // with the symbolic cylinder classification. For residue 0, use u=4096
  // so the omitted exponential term has n>=55.
  let directOpen = 0;
  let mismatches = [];
  for (let r = 0; r < MODULUS; r++) {
    const u = r === 0 ? MODULUS : r;
    const direct = directRepresentative(u);
    if (direct) directOpen++;
    if (direct !== open.has(r)) mismatches.push({ residue: r, u, direct });
  }

  if (mismatches.length !== 0) {
    throw new Error("direct representative verification failed: " +
      JSON.stringify(mismatches.slice(0, 10)));
  }

  const output = {
    family: "a=13*2^(23+32u)-24u-19, b=2a-13, u>=1",
    inverseDepth: DEPTH,
    parameterModulus: MODULUS,
    openPathCount: result.openPaths,
    openResidueCount: result.openResidueCount,
    excludedResidueCount: MODULUS - result.openResidueCount,
    openResidues: result.openResidues,
    directRepresentativesChecked: MODULUS,
    directOpenRepresentatives: directOpen,
    directMismatches: mismatches.length,
    symbolicNodesProcessed: result.processed,
    parameterSplits: result.splitNodes,
    deadPaths: result.deadPaths
  };
  process.stdout.write(JSON.stringify(output, null, 2) + "\n");
}

main();
