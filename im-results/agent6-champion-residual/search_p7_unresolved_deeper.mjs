#!/usr/bin/env node
"use strict";

// Deeper bounded follow-up for the eight depth-7 A/1 siblings left open by
// search_p7_last_hole.mjs. Uses Brent cycle detection (constant auxiliary
// memory), a 5M transition cap, and a wider side-cycle search.

const names = "ABCDEF";
const p7 = [
  "1RB", null, "1RC", null,
  "1LD", "0RF", "1RA", "0LE",
  "0LD", "1RC", "1RA", "0RE",
];
const unresolved = ["0LA", "0LC", "1LC", "1LD", "1RD", "0LE", "1RE", "1LF"];

function parseMove(move) {
  return { write: Number(move[0]), direction: move[1], next: names.indexOf(move[2]) };
}
function clone(c) {
  return { state: c.state, head: c.head, ones: new Set(c.ones) };
}
function same(a, b) {
  if (a.state !== b.state || a.head !== b.head || a.ones.size !== b.ones.size) return false;
  for (const x of a.ones) if (!b.ones.has(x)) return false;
  return true;
}
function step(table, c) {
  const slot = 2 * c.state + (c.ones.has(c.head) ? 1 : 0);
  const move = table[slot];
  if (move === null) return { kind: "hole", slot };
  const m = parseMove(move);
  if (m.write) c.ones.add(c.head);
  else c.ones.delete(c.head);
  c.head += m.direction === "R" ? 1 : -1;
  c.state = m.next;
  return { kind: "ok" };
}
function run(table, start, count) {
  const c = clone(start);
  const history = [clone(c)];
  for (let i = 0; i < count; i++) {
    const z = step(table, c);
    if (z.kind !== "ok") return { ...z, step: i, config: c, history };
    history.push(clone(c));
  }
  return { kind: "ok", config: c, history };
}
function classify(table, cap = 5_000_000) {
  const initial = { state: 0, head: 0, ones: new Set() };
  const tortoise = clone(initial);
  const hare = clone(initial);
  const first = step(table, hare);
  if (first.kind === "hole") return { kind: "hole", successfulMoves: 0, slot: first.slot };
  let n = 1, power = 1, period = 1;
  while (!same(tortoise, hare) && n < cap) {
    if (power === period) {
      Object.assign(tortoise, clone(hare));
      power *= 2;
      period = 0;
    }
    const z = step(table, hare);
    if (z.kind === "hole") return { kind: "hole", successfulMoves: n, slot: z.slot };
    n++;
    period++;
  }
  if (same(tortoise, hare)) return { kind: "lasso", lassoSteps: n, period };
  return { kind: "cap", cap };
}
function sideCycle(table, entryCap = 20, periodCap = 50, radiusCap = 50) {
  for (let entry = 0; entry <= entryCap; entry++) {
    const prefix = run(table, { state: 0, head: 0, ones: new Set() }, entry);
    if (prefix.kind !== "ok") continue;
    const start = prefix.config;
    for (let period = 1; period <= periodCap; period++) {
      const cycle = run(table, start, period);
      if (cycle.kind !== "ok") continue;
      const end = cycle.config;
      const delta = end.head - start.head;
      const right = delta >= 0;
      if (end.state !== start.state || delta === 0) continue;
      for (let radius = 0; radius <= radiusCap; radius++) {
        const boundary = right ? start.head - radius : start.head + radius;
        const onSide = x => right ? x >= boundary : x <= boundary;
        if (!onSide(start.head)) continue;
        if (!cycle.history.slice(0, period).every(c => onSide(c.head))) continue;
        let valid = true;
        for (const x of start.ones) {
          if (onSide(x) && !end.ones.has(x + delta)) { valid = false; break; }
        }
        if (!valid) continue;
        for (const y of end.ones) {
          if (onSide(y - delta) && !start.ones.has(y - delta)) { valid = false; break; }
        }
        if (valid) return { entry, period, right, boundary, delta };
      }
    }
  }
  return null;
}

const results = unresolved.map(move => {
  const child = p7.slice();
  child[1] = move;
  const outcome = classify(child, 5_000_000);
  if (outcome.kind === "cap") return { move, ...outcome, sideCycle: sideCycle(child, 20, 50, 50) };
  return { move, ...outcome };
});
console.log(JSON.stringify({
  cap: 5_000_000,
  sideCycleBounds: { entry: 20, period: 50, boundaryRadius: 50 },
  counts: {
    total: results.length,
    hole: results.filter(x => x.kind === "hole").length,
    lasso: results.filter(x => x.kind === "lasso").length,
    capped: results.filter(x => x.kind === "cap").length,
    sideCycle: results.filter(x => x.sideCycle).length
  },
  results
}, null, 2));
