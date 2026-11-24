#!/usr/bin/env node
"use strict";

// Exact Set-based carry census for h=0..256 in the two fourth-edge families.
// All integers are below 2^53 in this finite scan.

function firstEmpty(n, maxSteps = 10000) {
  let states = new Set([(n + 2) / 2]);
  let maxStates = 1;
  let maxAt = 1;
  for (let j = 1; j < Math.min(n, maxSteps); j++) {
    const C = n + 3 + j;
    const next = new Set();
    for (const c of states) {
      if ((c & 1) === 0) {
        next.add(c / 2);
        if ((C & 1) === 0) next.add((c + C) / 2);
      } else if ((C & 1) === 1) {
        next.add((c + C) / 2);
      }
    }
    states = next;
    if (states.size > maxStates) {
      maxStates = states.size;
      maxAt = j + 1;
    }
    if (states.size === 0) return { K: j + 1, maxStates, maxAt };
  }
  return { K: null, maxStates, maxAt };
}

const families = [
  { name: "I", n0: 5362, delta: 595056 },
  { name: "II", n0: 9538, delta: 703248 },
];

for (const family of families) {
  const rows = [];
  for (let h = 0; h <= 256; h++) {
    const n = family.n0 + family.delta * h;
    rows.push({ h, n, ...firstEmpty(n) });
  }
  const unresolved = rows.filter((r) => r.K === null);
  console.log(JSON.stringify({
    family: family.name,
    tested: rows.length,
    unresolved,
    top: rows.filter((r) => r.K !== null)
      .sort((a, b) => b.K - a.K)
      .slice(0, 20),
  }, null, 2));
}
