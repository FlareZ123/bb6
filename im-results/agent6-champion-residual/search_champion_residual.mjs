#!/usr/bin/env node
"use strict";

// Reproducible bounded search for first-hole sibling lasso/side-cycle witnesses
// in the champion-containing nine-hole residual. Lean replays every emitted
// witness with residualWitnessOK; this script is discovery, not proof.

const champion = [
  "1RB", "1RA", "1RC", null,
  "1LD", "0RF", "1RA", "0LE",
  "0LD", "1RC", "1RA", "0RE",
];
const initial = [
  "1RB", null, "1RC", null,
  "1LD", null, null, null,
  null, null, null, null,
];
const championPath = [
  "0LE", "1RC", "0LD", "1RA",
  "0RF", "0RE", "1RA", "1RA",
];
const stateNames = "ABCDEF";

function parseMove(move) {
  return {
    write: Number(move[0]),
    direction: move[1],
    next: stateNames.indexOf(move[2]),
  };
}

function step(table, config) {
  const slot = 2 * config.state + (config.ones.has(config.head) ? 1 : 0);
  const move = table[slot];
  if (move === null) return { kind: "hole", slot };
  const parsed = parseMove(move);
  if (parsed.write) config.ones.add(config.head);
  else config.ones.delete(config.head);
  config.head += parsed.direction === "R" ? 1 : -1;
  config.state = parsed.next;
  return { kind: "ok" };
}

function clone(config) {
  return {
    state: config.state,
    head: config.head,
    ones: new Set(config.ones),
  };
}

function key(config) {
  return String(config.state) + "|" + String(config.head) + "|" +
    [...config.ones].sort((a, b) => a - b).join(",");
}

function run(table, start, count) {
  const config = clone(start);
  const history = [clone(config)];
  for (let i = 0; i < count; i++) {
    const result = step(table, config);
    if (result.kind !== "ok") return { ...result, step: i, config, history };
    history.push(clone(config));
  }
  return { kind: "ok", config, history };
}

function firstHole(table, cap = 1_000_000) {
  const config = { state: 0, head: 0, ones: new Set() };
  for (let n = 0; n < cap; n++) {
    const result = step(table, config);
    if (result.kind !== "ok") return { ...result, step: n, config };
  }
  return { kind: "cap", cap };
}

function lasso(table, cap = 80) {
  const config = { state: 0, head: 0, ones: new Set() };
  const seen = new Map([[key(config), 0]]);
  for (let n = 1; n <= cap; n++) {
    const result = step(table, config);
    if (result.kind !== "ok") return null;
    const k = key(config);
    if (seen.has(k)) {
      const entry = seen.get(k);
      return { kind: "lasso", entry, period: n - entry, n };
    }
    seen.set(k, n);
  }
  return null;
}

function sideCycle(table, entryCap = 6, periodCap = 20, boundaryRadius = 10) {
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
      for (let radius = 0; radius <= boundaryRadius; radius++) {
        const boundary = right ? start.head - radius : start.head + radius;
        const onSide = x => right ? x >= boundary : x <= boundary;
        if (!onSide(start.head)) continue;
        if (!cycle.history.slice(0, period).every(c => onSide(c.head))) continue;
        let valid = true;
        for (const x of start.ones) {
          if (onSide(x) && !end.ones.has(x + delta)) {
            valid = false;
            break;
          }
        }
        if (!valid) continue;
        for (const y of end.ones) {
          if (onSide(y - delta) && !start.ones.has(y - delta)) {
            valid = false;
            break;
          }
        }
        if (valid) return { kind: "side", entry, period, right, boundary, delta };
      }
    }
  }
  return null;
}

const moves = [];
for (let next = 0; next < 6; next++) {
  for (let write = 0; write < 2; write++) {
    for (const direction of ["L", "R"]) {
      moves.push(String(write) + direction + stateNames[next]);
    }
  }
}

const table = initial.slice();
const levels = [];
const witnesses = [];
for (let depth = 0; depth < championPath.length; depth++) {
  const query = firstHole(table);
  if (query.kind !== "hole") {
    throw new Error("expected a finite first hole at depth " + depth +
      ", got " + query.kind);
  }
  const expectedMove = championPath[depth];
  const siblings = [];
  for (const move of moves) {
    if (move === expectedMove) continue;
    const child = table.slice();
    child[query.slot] = move;
    const witness = lasso(child, 80) ?? sideCycle(child, 6, 20, 10);
    if (witness) {
      const item = { depth, hole: query.slot, move, witness };
      siblings.push(item);
      witnesses.push(item);
    }
  }
  levels.push({
    depth,
    hole: stateNames[Math.floor(query.slot / 2)] + "/" + (query.slot % 2),
    successfulMoves: query.step,
    championMove: expectedMove,
    closedSiblingCount: siblings.length,
    openSiblingCount: 23 - siblings.length,
    witnesses: siblings,
  });
  table[query.slot] = expectedMove;
}

const holes = table.flatMap((move, slot) => move === null ? [slot] : []);
if (holes.length !== 1 || holes[0] !== 3) {
  throw new Error("expected only B/1 to remain undefined, got " + holes);
}
if (table.some((move, slot) => move !== champion[slot])) {
  throw new Error("champion path did not reconstruct the expected terminal partial table");
}

const openByDepth = levels.map(level => level.openSiblingCount);
const residualCount = openByDepth.reduce((a, b) => a + b, 0);
const residualMass = openByDepth.reduce(
  (sum, count, depth) => sum + BigInt(count) * 25n ** BigInt(8 - depth),
  0n,
);
const totalMass = 25n ** 9n;

console.log(JSON.stringify({
  initialTable: initial,
  championPath,
  levels,
  witnesses,
  witnessCount: witnesses.length,
  residualCount,
  openByDepth,
  terminalHole: "B/1",
  terminalPartialTable: table,
  residualCompletionMass: residualMass.toString(),
  originalCompletionMass: totalMass.toString(),
  closedCompletionMass: (totalMass - residualMass).toString(),
}, null, 2));
