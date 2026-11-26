"use strict";

// Deterministic BigInt stress test for the wider reverse-block quotient window.
// Run with: node wide_fit_bigint_check.js
// This checks generated legal blocks (not an exhaustive global theorem or C++ build).

let seed = 0x9e3779b9;
function rand() {
  seed ^= seed << 13;
  seed ^= seed >>> 17;
  seed ^= seed << 5;
  return seed >>> 0;
}

function digitWeight(b, k) {
  let d = 0n;
  for (let j = 0; j < k; j++) {
    if ((b >> BigInt(j)) & 1n) d += BigInt(j) * (1n << BigInt(j));
  }
  return d;
}

function candidates(q, k, z, y, strict) {
  const X = (z << BigInt(k)) + y;
  const F = q + BigInt(k);
  const maxB = (1n << BigInt(k)) - 1n;
  const first = X / F;
  const hits = [];
  for (const B of [first, first + 1n]) {
    if (B > maxB) continue;
    const c = X - q * B - digitWeight(B, k);
    if (c >= 0n && c < q && (!strict || (c >= 1n && c + 3n <= q))) {
      hits.push({ B, c });
    }
  }
  return hits;
}

let cases = 0;
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
    const X = q * B + digitWeight(B, k) + r;
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

console.log(JSON.stringify({
  cases,
  widerOnly,
  maxObservedX: maxObservedX.toString(),
  uint64Safe: maxObservedX < (1n << 64n)
}, null, 2));
