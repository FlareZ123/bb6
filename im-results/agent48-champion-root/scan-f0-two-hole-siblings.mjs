#!/usr/bin/env node
"use strict";

// Reproducible bounded scan of the 23 non-champion F/0 children after the
// first six refinements of the raw139 champion path. A side-cycle result is
// only a candidate until replayed by the Lean residual-witness checker.

const STATES = "ABCDEF";
const initial = [
  "1RB", null, "1RC", null, "1LD", null,
  null, null, null, null, null, null
];
const championPrefix = ["0LE", "1RC", "0LD", "1RA", "0RF", "0RE"];
const championF0Move = "1RA";
const f0Slot = 10;
const cap = 1_000_000;
const deepCap = 5_000_000;

function parseMove(x) {
  return { write: Number(x[0]), direction: x[1], next: STATES.indexOf(x[2]) };
}
function clone(c) { return { state: c.state, head: c.head, ones: new Set(c.ones) }; }
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
  if (m.write) c.ones.add(c.head); else c.ones.delete(c.head);
  c.head += m.direction === "R" ? 1 : -1;
  c.state = m.next;
  return { kind: "ok" };
}
function classify(table, limit) {
  const initialConfig = { state: 0, head: 0, ones: new Set() };
  const tortoise = clone(initialConfig), hare = clone(initialConfig);
  let z = step(table, hare);
  if (z.kind === "hole") return { kind: "hole", slot: z.slot, successfulMoves: 0 };
  let n = 1, power = 1, period = 1;
  while (!same(tortoise, hare) && n < limit) {
    if (power === period) {
      Object.assign(tortoise, clone(hare));
      power *= 2;
      period = 0;
    }
    z = step(table, hare);
    if (z.kind === "hole") return { kind: "hole", slot: z.slot, successfulMoves: n };
    n++;
    period++;
  }
  return same(tortoise, hare)
    ? { kind: "lasso", lassoSteps: n, period }
    : { kind: "cap", cap: limit };
}
function run(table, start, count) {
  const c = clone(start), history = [clone(start)];
  for (let i = 0; i < count; i++) {
    const z = step(table, c);
    if (z.kind !== "ok") return { ...z, step: i, config: c, history };
    history.push(clone(c));
  }
  return { kind: "ok", config: c, history };
}
function sideCycle(table, entryCap, periodCap, radiusCap) {
  for (let entry = 0; entry <= entryCap; entry++) {
    const pre = run(table, { state: 0, head: 0, ones: new Set() }, entry);
    if (pre.kind !== "ok") continue;
    const start = pre.config;
    for (let period = 1; period <= periodCap; period++) {
      const cyc = run(table, start, period);
      if (cyc.kind !== "ok") continue;
      const end = cyc.config, delta = end.head - start.head;
      const right = delta >= 0;
      if (end.state !== start.state || delta === 0) continue;
      for (let radius = 0; radius <= radiusCap; radius++) {
        const boundary = right ? start.head - radius : start.head + radius;
        const onSide = x => right ? x >= boundary : x <= boundary;
        if (!onSide(start.head) || !cyc.history.slice(0, period).every(c => onSide(c.head))) continue;
        let ok = true;
        for (const x of start.ones) {
          if (onSide(x) && !end.ones.has(x + delta)) { ok = false; break; }
        }
        if (!ok) continue;
        for (const y of end.ones) {
          if (onSide(y - delta) && !start.ones.has(y - delta)) { ok = false; break; }
        }
        if (ok) return { entry, period, right, boundary, delta };
      }
    }
  }
  return null;
}

const moves = [];
for (let q = 0; q < 6; q++)
  for (let w = 0; w < 2; w++)
    for (const d of ["L", "R"])
      moves.push(String(w) + d + STATES[q]);

// Reconstruct the exact six-step champion prefix rather than hardcoding p6.
const p6 = initial.slice();
for (const move of championPrefix) {
  const h = classify(p6, 100_000);
  if (h.kind !== "hole") throw new Error("champion prefix failed: " + JSON.stringify(h));
  p6[h.slot] = move;
}
if (p6[f0Slot] !== null || p6[1] !== null || p6[3] !== null)
  throw new Error("unexpected three-hole p6 parent");

const outcomes = [];
for (const f0Move of moves.filter(m => m !== championF0Move)) {
  const parent = p6.slice();
  parent[f0Slot] = f0Move;
  const first = classify(parent, cap);

  if (first.kind !== "hole") {
    const deep = first.kind === "cap" ? classify(parent, deepCap) : first;
    const cycle = deep.kind === "cap" ? sideCycle(parent, 50, 100, 100) : null;
    outcomes.push({
      f0Move, first, deep,
      sideCycle: cycle,
      closedByBoundedWitness: deep.kind === "lasso" || cycle !== null
    });
    continue;
  }

  const remainingHole = first.slot === 1 ? 3 : 1;
  const grandchildren = [];
  for (const assignedMove of [null, ...moves]) {
    if (assignedMove === null) {
      grandchildren.push({ move: "HALT", kind: "halt" });
      continue;
    }
    const child = parent.slice();
    child[first.slot] = assignedMove;
    const second = classify(child, cap);
    if (second.kind === "hole" && second.slot === remainingHole) {
      grandchildren.push({ move: assignedMove, kind: "secondHole", steps: second.successfulMoves });
    } else if (second.kind === "lasso") {
      grandchildren.push({ move: assignedMove, kind: "lasso", steps: second.lassoSteps, period: second.period });
    } else if (second.kind === "cap") {
      const cycle = sideCycle(child, 6, 20, 10);
      grandchildren.push({ move: assignedMove, kind: cycle ? "sideCycle" : "cap", sideCycle: cycle });
    } else {
      grandchildren.push({ move: assignedMove, kind: second.kind, slot: second.slot });
    }
  }
  const counts = {};
  for (const x of grandchildren) counts[x.kind] = (counts[x.kind] || 0) + 1;
  outcomes.push({
    f0Move, first, remainingHole, counts,
    closedGrandchildren: grandchildren.filter(x => x.kind !== "cap").length,
    unresolvedGrandchildren: grandchildren.filter(x => x.kind === "cap").map(x => x.move),
    grandchildren
  });
}

const summary = {
  f0Siblings: outcomes.length,
  firstHoleWithin1M: outcomes.filter(x => x.first.kind === "hole").length,
  capAt1M: outcomes.filter(x => x.first.kind === "cap").length,
  resolvedGrandchildren: outcomes.reduce((n, x) => n + (x.closedGrandchildren || 0), 0),
  unresolvedGrandchildren: outcomes.reduce((n, x) => n + (x.unresolvedGrandchildren?.length || 0), 0),
  deeperSideCycleParents: outcomes.filter(x => x.closedByBoundedWitness).map(x => x.f0Move)
};
console.log(JSON.stringify({
  sourceModel: "raw139 champion path after first six refinements; F/0 is the next hole",
  cap, deepCap,
  deepSideCycleBounds: { entry: 50, period: 100, radius: 100 },
  summary, outcomes
}, null, 2));
