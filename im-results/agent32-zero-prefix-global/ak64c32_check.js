#!/usr/bin/env node
"use strict";

// Reproducible experimental quotient for the Machine C accelerator.
// Coordinates A,K use exact values below 2 and residues modulo 64 above;
// coordinate C uses exact values below 4 and residues modulo 32 above.
// This is a finite over-approximation, not a Lean theorem by itself.

const assert = require("node:assert/strict");

const A_BASE = 2, A_MOD = 64, A_N = A_BASE + A_MOD;
const K_BASE = 2, K_MOD = 64, K_N = K_BASE + K_MOD;
const C_BASE = 4, C_MOD = 32, C_N = C_BASE + C_MOD;
const TOTAL = A_N * K_N * C_N;

function quotient(x, base, mod) {
  return x < base ? x : base + ((x - base) % mod);
}
const qA = x => quotient(x, A_BASE, A_MOD);
const qK = x => quotient(x, K_BASE, K_MOD);
const qC = x => quotient(x, C_BASE, C_MOD);

function representatives(u, base, mod) {
  return u < base ? [u] : [u, u + mod];
}
const repsA = Array.from({length:A_N}, (_,u) => representatives(u,A_BASE,A_MOD));
const repsK = Array.from({length:K_N}, (_,u) => representatives(u,K_BASE,K_MOD));
const repsC = Array.from({length:C_N}, (_,u) => representatives(u,C_BASE,C_MOD));

function encode(a,k,c) {
  return (a * K_N + k) * C_N + c;
}

// Exact nine-clause transition function from BB6CLine.nextC.
function nextC(a,k,c) {
  if (c === 1) return [a,k+1,0];
  if (c === 2) return null;
  if (c === 3) return [a,k+2,1];

  if (c === 0) {
    if (a === 0) return [1,0,2*k+2];
    if (a === 1) return k === 0 ? [5,0,1] : [2,2,2*k-1];
    return [a-2,1,2*k+1];
  }

  if (a === 0) {
    return (k % 2 === 0)
      ? [2*k+2,2,c-3]
      : [2*k+3,0,c];
  }
  return [a-1,k+1,c-1];
}

function buildClosure() {
  const seen = new Uint8Array(TOTAL);
  const queue = new Int32Array(TOTAL);
  let head = 0, tail = 0, representativeEdges = 0;

  const start = encode(qA(5),qK(0),qC(1));
  seen[start] = 1;
  queue[tail++] = start;

  while (head < tail) {
    const id = queue[head++];
    const c = id % C_N;
    const k = Math.floor(id / C_N) % K_N;
    const a = Math.floor(id / (K_N*C_N));

    for (const aa of repsA[a]) {
      for (const kk of repsK[k]) {
        for (const cc of repsC[c]) {
          const out = nextC(aa,kk,cc);
          if (out === null) continue;
          representativeEdges++;
          const target = encode(qA(out[0]),qK(out[1]),qC(out[2]));
          if (!seen[target]) {
            seen[target] = 1;
            queue[tail++] = target;
          }
        }
      }
    }
  }

  return {seen,reachableStates:tail,representativeEdges};
}

const closure = buildClosure();
const {seen,reachableStates,representativeEdges} = closure;
const reachable = (a,k,c) => !!seen[encode(qA(a),qK(k),qC(c))];

const resetAllowed = Array.from({length:64},(_,j)=>j)
  .filter(j=>reachable(2*j+1,3*j+4,0));
const resetExcluded = Array.from({length:64},(_,j)=>j)
  .filter(j=>!resetAllowed.includes(j));
const sideAllowed = Array.from({length:32},(_,n)=>n)
  .filter(n=>reachable(0,4*n,24*n+23));
const sideExcluded = Array.from({length:32},(_,n)=>n)
  .filter(n=>!sideAllowed.includes(n));

const targetCells = {
  reset_j58: {raw:[117,178,0], abstract:[qA(117),qK(178),qC(0)], reachable:reachable(117,178,0)},
  reset_j59: {raw:[119,181,0], abstract:[qA(119),qK(181),qC(0)], reachable:reachable(119,181,0)},
  side_n16: {raw:[0,64,407], abstract:[qA(0),qK(64),qC(407)], reachable:reachable(0,64,407)}
};

assert.equal(TOTAL,156816);
assert.equal(reachableStates,77020);
assert.equal(representativeEdges,576340);
assert.deepEqual(resetAllowed,[0,2,6,8,10,11,14,15,18,23,24,26,27,30,31,32,34,38,39,40,42,43,46,47,50,55,56,62,63]);
assert.deepEqual(sideAllowed,[2,3,4,6,7,8,10,11,12,14,15,18,19,20,22,23,24,26,27,28,30,31]);
assert.equal(targetCells.reset_j58.reachable,false);
assert.equal(targetCells.reset_j59.reachable,false);
assert.equal(targetCells.side_n16.reachable,false);

// Recheck closure independently of the queue traversal: every representative
// edge from every marked abstract state must remain inside the marked set.
for(let a=0;a<A_N;a++) for(let k=0;k<K_N;k++) for(let c=0;c<C_N;c++) {
  if(!seen[encode(a,k,c)]) continue;
  for(const aa of repsA[a]) for(const kk of repsK[k]) for(const cc of repsC[c]) {
    const out=nextC(aa,kk,cc);
    assert(out===null || seen[encode(qA(out[0]),qK(out[1]),qC(out[2]))]);
  }
}

console.log(JSON.stringify({
  quotient:"A: exact below 2 / mod64; K: exact below 2 / mod64; C: exact below 4 / mod32",
  vertices:TOTAL,
  reachableStates,
  representativeEdges,
  resetAllowedJMod64:resetAllowed,
  resetExcludedJMod64:resetExcluded,
  sideAllowedNMod32:sideAllowed,
  sideExcludedNMod32:sideExcluded,
  targetCells
},null,2));
