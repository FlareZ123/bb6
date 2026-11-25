#!/usr/bin/env node
"use strict";

// Deeper side-cycle search for the seven F/0 siblings not closed by the
// 100-entry / 200-period scan in scan-f0-two-hole-siblings.mjs.

const names = "ABCDEF";
const p6 = ["1RB", null, "1RC", null, "1LD", "0RF", "1RA", "0LE", "0LD", "1RC", null, "0RE"];
const f0 = 10;
const candidates = ["0LB", "0LC", "1LC", "0LD", "1RD", "0LE", "0RE"];

function parseMove(x) { return { write: Number(x[0]), direction: x[1], next: names.indexOf(x[2]) }; }
function clone(c) { return { state: c.state, head: c.head, ones: new Set(c.ones) }; }
function same(a, b) {
  if (a.state !== b.state || a.head !== b.head || a.ones.size !== b.ones.size) return false;
  for (const x of a.ones) if (!b.ones.has(x)) return false;
  return true;
}
function step(t, c) {
  const slot = 2 * c.state + (c.ones.has(c.head) ? 1 : 0), m = t[slot];
  if (m === null) return { kind: "hole", slot };
  const z = parseMove(m);
  if (z.write) c.ones.add(c.head); else c.ones.delete(c.head);
  c.head += z.direction === "R" ? 1 : -1;
  c.state = z.next;
  return { kind: "ok" };
}
function run(t, start, n) {
  const c = clone(start), history = [clone(start)];
  for (let i = 0; i < n; i++) {
    const z = step(t, c);
    if (z.kind !== "ok") return { ...z, step: i, config: c, history };
    history.push(clone(c));
  }
  return { kind: "ok", config: c, history };
}
function classify(t, cap) {
  const init = { state: 0, head: 0, ones: new Set() }, tor = clone(init), hare = clone(init);
  let z = step(t, hare);
  if (z.kind === "hole") return { kind: "hole", slot: z.slot, successfulMoves: 0 };
  let n = 1, power = 1, period = 1;
  while (!same(tor, hare) && n < cap) {
    if (power === period) { Object.assign(tor, clone(hare)); power *= 2; period = 0; }
    z = step(t, hare);
    if (z.kind === "hole") return { kind: "hole", slot: z.slot, successfulMoves: n };
    n++; period++;
  }
  return same(tor, hare) ? { kind: "lasso", lassoSteps: n, period } : { kind: "cap", cap };
}
function sideCycle(t, entryCap, periodCap, radiusCap) {
  for (let entry = 0; entry <= entryCap; entry++) {
    const pre = run(t, { state: 0, head: 0, ones: new Set() }, entry);
    if (pre.kind !== "ok") continue;
    const start = pre.config;
    for (let period = 1; period <= periodCap; period++) {
      const cyc = run(t, start, period);
      if (cyc.kind !== "ok") continue;
      const end = cyc.config, delta = end.head - start.head, right = delta >= 0;
      if (end.state !== start.state || delta === 0) continue;
      for (let radius = 0; radius <= radiusCap; radius++) {
        const boundary = right ? start.head - radius : start.head + radius;
        const onSide = x => right ? x >= boundary : x <= boundary;
        if (!onSide(start.head) || !cyc.history.slice(0, period).every(c => onSide(c.head))) continue;
        let ok = true;
        for (const x of start.ones) if (onSide(x) && !end.ones.has(x + delta)) { ok = false; break; }
        if (!ok) continue;
        for (const y of end.ones) if (onSide(y - delta) && !start.ones.has(y - delta)) { ok = false; break; }
        if (ok) return { entry, period, right, boundary, delta };
      }
    }
  }
  return null;
}

const outcomes = candidates.map(move => {
  const t = p6.slice(); t[f0] = move;
  const bounded = classify(t, 5_000_000);
  const witness = bounded.kind === "cap" ? sideCycle(t, 200, 400, 400) : null;
  return { move, bounded, witness };
});
console.log(JSON.stringify({
  cap: 5_000_000,
  sideCycleBounds: { entry: 200, period: 400, radius: 400 },
  outcomes
}, null, 2));
