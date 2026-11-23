"use strict";

/*
  Six-state, two-symbol, blank-start, five-step translated-blank drift family.
  Node.js >= 16; exact integers, no dependencies.
  The five fixed instructions are:
    A/0 -> 1 d B       B/0 -> 1 (-d) C
    C/1 -> 0 d D       D/1 -> 0 (-d) E
    E/0 -> 0 d A.
  Guards: B!=A, D!=C, E!=A,B.
  All unlisted instructions are arbitrary (25 choices each).

  This script checks all 1200 candidate assignments, their five actual
  blank-tape moves, and all 719400 unordered pair conflicts.  Its main
  assertions are independent of any stochastic sampling or BigInt bounds.
*/

const assert = require("node:assert/strict");
const states = [0, 1, 2, 3, 4, 5];
const dirs = [-1, 1];
const name = s => "ABCDEF"[s];
const slot = (s, bit) => s * 2 + bit;
const eq = (a, b) =>
  a.w === b.w && a.d === b.d && a.to === b.to;

function makeFamily(d, B, C, D, E) {
  assert(states.includes(B) && B !== 0);
  assert(states.includes(C) && states.includes(D) && C !== D);
  assert(states.includes(E) && E !== 0 && E !== B);
  assert(d === 1 || d === -1);
  const rows = new Map();
  function put(s, bit, w, move, to) {
    const key = slot(s, bit);
    assert(!rows.has(key), "duplicate fixed input row");
    rows.set(key, {w, d: move, to});
  }
  put(0, 0, 1, d, B);
  put(B, 0, 1, -d, C);
  put(C, 1, 0, d, D);
  put(D, 1, 0, -d, E);
  put(E, 0, 0, d, 0);
  assert.equal(rows.size, 5);
  return {d, B, C, D, E, rows};
}

function allFamilies() {
  const out = [];
  for (const d of dirs)
    for (const B of states.filter(x => x !== 0))
      for (const C of states)
        for (const D of states.filter(x => x !== C))
          for (const E of states.filter(x => x !== 0 && x !== B))
            out.push(makeFamily(d, B, C, D, E));
  assert.equal(out.length, 1200);
  return out;
}

function simulateFive(family) {
  let state = 0, head = 0;
  const ones = new Set();
  const trace = [{state, head, ones: []}];
  for (let i = 0; i < 5; i++) {
    const bit = +ones.has(head);
    const action = family.rows.get(slot(state, bit));
    assert(action, "missing actually-read action");
    if (action.w) ones.add(head);
    else ones.delete(head);
    state = action.to;
    head += action.d;
    trace.push({state, head, ones: [...ones].sort((a, b) => a-b)});
  }
  assert.equal(state, 0);
  assert.equal(head, family.d);
  assert.equal(ones.size, 0);
  return trace;
}

function conflict(p, q) {
  for (const [s, t] of p.rows) {
    const u = q.rows.get(s);
    if (u !== undefined && !eq(t, u)) return s;
  }
  return null;
}

function tableKey(family) {
  return [...family.rows].sort((a, b) => a[0]-b[0]).map(
    ([k, t]) => [k, t.w, t.d, t.to].join(":")
  ).join(";");
}

function run() {
  const items = allFamilies();
  const keys = new Set();
  for (const t of items) {
    simulateFive(t);
    const key = tableKey(t);
    assert(!keys.has(key), "duplicate partial table");
    keys.add(key);
  }
  let pairs = 0;
  for (let i = 0; i < items.length; i++)
    for (let j = i + 1; j < items.length; j++) {
      assert.notEqual(conflict(items[i], items[j]), null,
        "two distinct cylinders could overlap");
      pairs++;
    }
  assert.equal(pairs, 719400);

  // Distinct pairwise-incompatible 5-row cylinders each have 25^7
  // completions; all 25 transition choices are allowed for free rows.
  const mass = BigInt(items.length) * 25n**7n;
  const total = 25n**12n;
  assert.equal(mass, 7324218750000n);
  assert.equal(total, 59604644775390625n);
  assert.equal(mass * 1000000n / total, 122n); // floor(ppm)
  const example = items.find(x =>
    x.d === 1 && x.B === 1 && x.C === 2 && x.D === 3 && x.E === 4);
  assert(example);
  const exampleTrace = simulateFive(example).map(x => ({
    ...x, state: name(x.state)
  }));
  const out = {
    familyCount: items.length,
    checkedDistinctPairs: pairs,
    fixedRowsPerTable: 5,
    arbitraryRowsPerTable: 7,
    mass: mass.toString(),
    rawTableUniverse: total.toString(),
    exactFraction: "1200/9765625",
    percentage: 0.012288,
    exampleRLEFixedRows: [
      "A/0:1RB", "B/0:1LC", "C/1:0RD", "D/1:0LE", "E/0:0RA"
    ],
    exampleTrace
  };
  console.log(JSON.stringify(out, null, 2));
}

run();
