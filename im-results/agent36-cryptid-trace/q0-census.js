#!/usr/bin/env node
/*
  Exact integer arithmetic census for the source-proved B/E normalizer
  after Cryptid D fixed-tail E,p=2 reset at Q=0.

  Use: node im-results/agent36-cryptid-trace/q0-census.js
  This enumerates the abstract, Lean source-certified guarded
  normalizer, not unproved physical machine steps or a blank-root orbit.

  The Y3 terminal predicate is source-sound by Y3SafeNormalizer.lean.
  Y3CylinderLift.lean gives a 3-adic infinite-cylinders theorem.
*/
"use strict";
const MOD = 2187n; // 3^7 = 3^(initial q+p + 1), with q=0,p=6.
function normalize(k) {
  let a = 8n*k + 5n, q = 0n, p = 6n, n = 0;
  while (true) {
    if (a % 3n === 2n && q > 0n) {
      a = 8n*((a-2n)/3n)+10n;
      q -= 1n;
    } else if (a % 3n === 1n && a >= 4n && p >= 3n) {
      a = 8n*((a-4n)/3n)+9n;
      q += 2n;
      p -= 3n;
    } else break;
    ++n;
    if (n > 6) throw new Error("violated rank-decrease bound");
  }
  const cls =
    a % 3n === 0n ? "A" :
    a % 3n === 2n && q === 0n ? "B0" :
    a % 3n === 1n && p === 0n
      ? "E0q" + (q % 3n).toString() :
    a % 3n === 1n && p === 1n ? "E1" : "OTHER";
  return {a,q,p,n,cls};
}
const counts = {}, bad = [];
for (let r = 0n; r < MOD; r++) {
  const result = normalize(r);
  counts[result.cls] = (counts[result.cls] || 0)+1;
  if (!["A","B0","E0q0","E1"].includes(result.cls))
    bad.push(Number(r));
}
console.log(JSON.stringify({
  modulus: Number(MOD),
  counts,
  safeCount: Number(MOD)-bad.length,
  residualCount: bad.length,
  residuals: bad
},null,2));
