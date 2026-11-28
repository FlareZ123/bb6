#!/usr/bin/env node
"use strict";

/*
 * Finite side-zipper witness discovery for the four challenging Raw42 children.
 *
 * This deliberately does NOT prove nonhalting. It enumerates finite machine
 * paths, emits candidate entry/period/side/boundary tuples, and leaves every
 * truth claim to Lean's zipCycle + zipCycle_sound in the generated .lean files.
 *
 * Defaults reproduce 9,9,4,9 second-level and 147,123,182,105 third-level
 * proposed witnesses (respectively B1 = 0LE,1LE,1RE,1LB); some overlap cases
 * are already source-accepted and the full 1LB child is independently closed.
 *
 * Usage:
 *     node discover_short_zip_v1.js > raw42-short-zip-candidates.json
 *
 * Nodes have no implicit halting step: 24 nonhalting moves are enumerated
 * at each queried undefined slot; the halt branch is handled by the existing
 * full-cover infrastructure, not by this candidate discovery routine.
 */

const PREFIX = {
  A0: [1, +1, "B"],
  B0: [1, +1, "C"],
  C0: [0, +1, "D"],
  D0: [1, -1, "D"],
  D1: [0, -1, "B"]
};
const CHOICES = {
  ZeroLE: [0, -1, "E"],
  OneLE: [1, -1, "E"],
  OneRE: [1, +1, "E"],
  OneLB: [1, -1, "B"]
};
const STATES = "ABCDEF";
const MOVES = [];
for (let write = 0; write <= 1; ++write)
  for (const dir of [-1, +1])
    for (const next of STATES)
      MOVES.push({name: `${write}${dir === +1 ? "R" : "L"}${next}`,
                  transition: [write, dir, next]});

function simulate(table, maxSteps) {
  let state = "A", head = 0;
  const ones = new Set(), path = [];
  for (let t = 0; t <= maxSteps; ++t) {
    const slot = state + (ones.has(head) ? "1" : "0");
    path.push({state, head, ones: new Set(ones), slot, t});
    const move = table[slot];
    if (move === undefined) return {path, stop: "unknown", slot};
    const [write, dir, next] = move;
    if (write === 1) ones.add(head);
    else ones.delete(head);
    head += dir;
    state = next;
  }
  return {path, stop: "time-cap"};
}

/* Exact comparison on the appropriate infinite half-tapes: all non-listed
 * positions are blank, and the second configuration is head-shift aligned.
 */
function halfEqual(a, b, right, boundary, delta) {
  const onSide = x => right ? x >= boundary : x <= boundary;
  for (const x of a.ones) {
    if (onSide(x) && !b.ones.has(x + delta)) return false;
  }
  for (const x of b.ones) {
    const y = x - delta;
    if (onSide(y) && !a.ones.has(y)) return false;
  }
  return true;
}

/* The head stays on one side of boundary throughout the period; translated
 * tape tails agree. The Lean kernel later decides zipCycle for the exact
 * machine and witness, using the project's formally proved checker.
 */
function findZip(path, maxEntry, maxPeriod) {
  for (let entry = 0; entry < Math.min(maxEntry, path.length - 1); ++entry) {
    let lo = Infinity, hi = -Infinity;
    for (let period = 1;
         period <= maxPeriod && entry + period < path.length;
         ++period) {
      const touched = path[entry + period - 1].head;
      lo = Math.min(lo, touched);
      hi = Math.max(hi, touched);
      const a = path[entry], b = path[entry + period];
      if (a.state !== b.state) continue;
      const delta = b.head - a.head;
      if (delta <= 0 && halfEqual(a, b, false, hi, delta))
        return {entry, period, right: false, boundary: hi, delta};
      if (delta >= 0 && halfEqual(a, b, true, lo, delta))
        return {entry, period, right: true, boundary: lo, delta};
    }
  }
  return null;
}

function exploreBranch(name, bound) {
  const base = {...PREFIX, B1: CHOICES[name]};
  let first = simulate(base, bound.maxSteps);
  if (first.stop !== "unknown") throw Error(name + ": first unresolved slot not queried");
  const secondSlot = first.slot;
  const second = [], third = [], unresolved = [];
  for (const m2 of MOVES) {
    const p2 = {...base, [secondSlot]: m2.transition};
    const t2 = simulate(p2, bound.maxSteps);
    const c2 = findZip(t2.path, bound.maxEntry, bound.maxPeriod);
    if (c2 !== null) {
      second.push({secondSlot, secondMove: m2.name, ...c2});
      continue;
    }
    if (t2.stop !== "unknown") {
      unresolved.push({secondSlot, secondMove: m2.name, reason: t2.stop});
      continue;
    }
    const thirdSlot = t2.slot;
    for (const m3 of MOVES) {
      const p3 = {...p2, [thirdSlot]: m3.transition};
      const t3 = simulate(p3, bound.maxSteps);
      const c3 = findZip(t3.path, bound.maxEntry, bound.maxPeriod);
      if (c3 !== null)
        third.push({secondSlot, secondMove: m2.name,
                    thirdSlot, thirdMove: m3.name, ...c3});
    }
  }
  return {branch: name, secondSlot, second, third, unresolved,
    counts: {second: second.length, third: third.length,
             secondCandidates: MOVES.length}};
}

const options = {maxSteps: 160, maxEntry: 100, maxPeriod: 130};
const results = Object.keys(CHOICES).map(name => exploreBranch(name, options));
const summary = {
  generator: "im-results/agent32-raw42/discover_short_zip_v1.js",
  searchLimits: options,
  requiresLeanVerification: true,
  totalSecond: results.reduce((x,r) => x+r.second.length, 0),
  totalThird: results.reduce((x,r) => x+r.third.length, 0),
  branches: results.map(r => ({name:r.branch, ...r.counts}))
};
process.stdout.write(JSON.stringify({summary, results}, null, 2) + "\n");
