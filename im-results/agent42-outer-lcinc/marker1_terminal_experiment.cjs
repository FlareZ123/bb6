#!/usr/bin/env node
"use strict";

// Exact-table finite simulator for the S0 terminal section with marker 0 or 1.
// State/head convention: state 0..5, head coordinate 0, blank tape outside
// the finite S0Config word. A halt is reported when the next transition query
// from state 0 reading 1 is undefined; "steps" counts successful transitions.

function transition(q, bit) {
  switch (q) {
    case 0: return bit ? null : [1, +1, 1];
    case 1: return bit ? [0, +1, 5] : [1, -1, 2];
    case 2: return bit ? [0, -1, 3] : [1, +1, 4];
    case 3: return bit ? [1, +1, 1] : [0, -1, 2];
    case 4: return bit ? [1, +1, 4] : [1, +1, 0];
    case 5: return bit ? [0, +1, 3] : [1, +1, 4];
    default: throw new Error("invalid state " + q);
  }
}

function initialTape(A, L, marker) {
  if (!Number.isSafeInteger(A) || A < 1) throw new Error("A must be >= 1");
  if (!Number.isSafeInteger(L) || L < 1) throw new Error("L must be >= 1");
  const markerWord = marker === 0 ? [0, 1] : [1, 0, 1];
  const left = [
    ...Array(3 * A).fill(1), // binDec(A,0) = d1pow(A)
    ...markerWord,
    0, 0, 1,                 // d0
    ...Array(3 * L).fill(1), // binDec(L,0) = d1pow(L)
    1, 1, 0, 1, 1, 1         // lh
  ];
  const right = [0, 1, 1, 1, 0, 0, 1, 1, 1]; // s0RightFacing(0)
  const ones = new Set();
  for (let i = 0; i < left.length; i++) if (left[i]) ones.add(-i);
  for (let i = 0; i < right.length; i++) if (right[i]) ones.add(i + 1);
  return ones;
}

function run(A, L, marker, maxSteps) {
  const ones = initialTape(A, L, marker);
  let q = 3, h = 0, minHead = 0, maxHead = 0;
  for (let step = 0; step < maxSteps; step++) {
    const action = transition(q, ones.has(h) ? 1 : 0);
    if (action === null) {
      return { marker, A, L, halted: true, steps: step, finalState: q,
        finalHead: h, ones: ones.size, minHead, maxHead };
    }
    const [write, move, next] = action;
    if (write) ones.add(h); else ones.delete(h);
    h += move;
    q = next;
    if (h < minHead) minHead = h;
    if (h > maxHead) maxHead = h;
  }
  return { marker, A, L, halted: false, horizon: maxSteps, finalState: q,
    finalHead: h, ones: ones.size, minHead, maxHead };
}

function main(argv) {
  const [markerText, aText, lText, limitText] = argv;
  if (markerText === "--grid") {
    const limit = Number(aText || 1000000);
    for (const marker of [0, 1]) {
      for (let A = 1; A <= 5; A++) {
        for (let L = 1; L <= 6; L++) {
          console.log(JSON.stringify(run(A, L, marker, limit)));
        }
      }
    }
    return;
  }
  const marker = Number(markerText);
  const A = Number(aText);
  const L = Number(lText);
  const limit = Number(limitText || 1000000);
  if (![0, 1].includes(marker)) throw new Error("marker must be 0 or 1");
  console.log(JSON.stringify(run(A, L, marker, limit), null, 2));
}

main(process.argv.slice(2));
