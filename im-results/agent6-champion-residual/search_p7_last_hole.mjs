#!/usr/bin/env node
"use strict";

// Classify all 23 ordinary A/1 children of the champion path at depth 7.
// Each child has only B/1 undefined. A hit at B/1 is a candidate lastHole
// leaf; an exact lasso or side cycle is a nonhalting leaf. Discovery only:
// the Lean certificates must replay each emitted witness.

const stateNames = "ABCDEF";
const p7 = [
  "1RB", null, "1RC", null,
  "1LD", "0RF", "1RA", "0LE",
  "0LD", "1RC", "1RA", "0RE",
];

function parseMove(move) {
  return { write: Number(move[0]), direction: move[1], next: stateNames.indexOf(move[2]) };
}
function key(c) {
  return String(c.state) + "|" + String(c.head) + "|" +
    [...c.ones].sort((a, b) => a - b).join(",");
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
function clone(c) {
  return { state: c.state, head: c.head, ones: new Set(c.ones) };
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
function classify(table, cap = 1_000_000) {
  const c = { state: 0, head: 0, ones: new Set() };
  const seen = new Map([[key(c), 0]]);
  for (let n = 0; n < cap; n++) {
    const z = step(table, c);
    if (z.kind === "hole") return { kind: "hole", successfulMoves: n, slot: z.slot };
    const k = key(c);
    if (seen.has(k)) {
      const entry = seen.get(k);
      return { kind: "lasso", entry, period: n + 1 - entry };
    }
    seen.set(k, n + 1);
  }
  return { kind: "cap", cap };
}
function sideCycle(table, entryCap = 6, periodCap = 20, radiusCap = 10) {
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

const moves = [];
for (let q = 0; q < 6; q++) {
  for (let w = 0; w < 2; w++) {
    for (const d of ["L", "R"]) moves.push(String(w) + d + stateNames[q]);
  }
}

const results = [];
for (const move of moves) {
  if (move === "1RA") continue; // champion continuation
  const child = p7.slice();
  child[1] = move; // A/1
  const outcome = classify(child);
  if (outcome.kind === "cap") {
    const witness = sideCycle(child);
    results.push({ move, ...outcome, sideCycle: witness });
  } else {
    results.push({ move, ...outcome });
  }
}
const counts = {
  total: results.length,
  haltAtB1: results.filter(x => x.kind === "hole" && x.slot === 3).length,
  lasso: results.filter(x => x.kind === "lasso").length,
  capped: results.filter(x => x.kind === "cap").length,
  cappedWithSideCycle: results.filter(x => x.kind === "cap" && x.sideCycle).length,
};
console.log(JSON.stringify({ parent: p7, hole: "A/1", remainingHole: "B/1", counts, results }, null, 2));
