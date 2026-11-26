"use strict";

// Deterministic BigInt stress test for the wider reverse-block quotient window.
// Run with: node wide_fit_bigint_check.js
// Also checks the modular first-jump subset-sum loop against direct enumeration.
// This is generated arithmetic evidence, not an exhaustive global theorem or C++ build.

let seed = 0x9e3779b9;
function rand() {
  seed ^= seed << 13;
  seed ^= seed >>> 17;
  seed ^= seed << 5;
  return seed >>> 0;
}

function digitWeightLoop(b, k) {
  let d = 0n;
  for (let j = 0; j < k; j++) {
    if ((b >> BigInt(j)) & 1n) d += BigInt(j) * (1n << BigInt(j));
  }
  return d;
}

// BigInt translation of block_reverse.hpp's fixed index-bit masks.
function digitWeightMask(b) {
  return (b & 0xAAAAAAAAAAAAAAAAn)
    + 2n * (b & 0xCCCCCCCCCCCCCCCCn)
    + 4n * (b & 0xF0F0F0F0F0F0F0F0n)
    + 8n * (b & 0xFF00FF00FF00FF00n)
    + 16n * (b & 0xFFFF0000FFFF0000n)
    + 32n * (b & 0xFFFFFFFF00000000n);
}

function jumpLoop(q, k, Y) {
  const M = 1n << BigInt(k);
  let residues = new Set([String(Y % M)]);
  for (let j = 0; j < k; j++) {
    const shift = ((q + BigInt(j)) * (1n << BigInt(j))) % M;
    const next = new Set(residues);
    for (const r of residues) next.add(String((BigInt(r) - shift + M) % M));
    residues = next;
  }
  return residues;
}

function jumpDirect(q, k, Y) {
  const M = 1n << BigInt(k);
  const residues = new Set();
  for (let B = 0n; B < M; B++) {
    const S = q * B + digitWeightLoop(B, k);
    residues.add(String((Y - S % M + M) % M));
  }
  return residues;
}

function candidates(q, k, z, y, strict) {
  const X = (z << BigInt(k)) + y;
  const F = q + BigInt(k);
  const maxB = (1n << BigInt(k)) - 1n;
  const first = X / F;
  const hits = [];
  for (const B of [first, first + 1n]) {
    if (B > maxB) continue;
    const c = X - q * B - digitWeightLoop(B, k);
    if (c >= 0n && c < q && (!strict || (c >= 1n && c + 3n <= q))) {
      hits.push({ B, c });
    }
  }
  return hits;
}

let cases = 0;
let maskChecks = 0;
let widerOnly = 0;
let maxObservedX = 0n;
for (let k = 1; k <= 26; k++) {
  const minQ = (1n << BigInt(k + 1)) - BigInt(k);
  const maxQ = 200000003n - BigInt(k);
  if (minQ > maxQ) continue;
  const span = Number(maxQ - minQ + 1n);
  const mask = (1n << BigInt(k)) - 1n;

  for (let i = 0; i < 1000; i++) {
    const q = minQ + BigInt(rand() % span);
    const B = BigInt(rand()) & mask;
    const r = BigInt(rand()) % q;
    const D = digitWeightLoop(B, k);
    if (D !== digitWeightMask(B)) throw new Error(`digitWeight mask mismatch at k=${k}`);
    maskChecks++;
    const X = q * B + D + r;
    const z = X >> BigInt(k);
    const y = X & mask;
    const F = q + BigInt(k);

    if (z >= F || X >= (1n << 64n)) throw new Error("range violation");
    const broad = candidates(q, k, z, y, false);
    if (broad.length !== 1 || broad[0].B !== B || broad[0].c !== r) {
      throw new Error(`broad mismatch at k=${k}`);
    }

    const strict = candidates(q, k, z, y, true);
    const shouldPass = r >= 1n && r + 3n <= q;
    if (shouldPass) {
      if (strict.length !== 1 || strict[0].B !== B || strict[0].c !== r) {
        throw new Error(`strict acceptance mismatch at k=${k}`);
      }
    } else if (strict.length !== 0) {
      throw new Error(`strict rejection mismatch at k=${k}`);
    }

    if (BigInt(k) * (1n << BigInt(k)) > q) widerOnly++;
    if (X > maxObservedX) maxObservedX = X;
    cases++;
  }
}

let jumpComparisons = 0;
let jumpResidues = 0;
for (let k = 1; k <= 12; k++) {
  const M = 1n << BigInt(k);
  for (let i = 0; i < 64; i++) {
    const q = BigInt(rand() % 200000003 + 1);
    const Y = BigInt(rand()) % M;
    const byLoop = jumpLoop(q, k, Y);
    const byDirect = jumpDirect(q, k, Y);
    if (byLoop.size !== byDirect.size || [...byDirect].some(r => !byLoop.has(r))) {
      throw new Error(`jump residue mismatch at k=${k}`);
    }
    jumpComparisons++;
    jumpResidues += byDirect.size;
  }
}

console.log(JSON.stringify({
  cases,
  maskChecks,
  jumpComparisons,
  jumpResidues,
  widerOnly,
  maxObservedX: maxObservedX.toString(),
  uint64Safe: maxObservedX < (1n << 64n)
}, null, 2));
