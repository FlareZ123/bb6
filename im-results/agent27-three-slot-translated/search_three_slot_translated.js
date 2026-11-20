#!/usr/bin/env node
"use strict";

/*
 * Bounded discovery of blank-root translated finite-support cylinders.
 *
 * This is an executable discovery mirror of the current Lean checkers, not
 * a proof.  Accepted cylinders must be checked with finiteTranslatedCheck
 * / finiteTranslatedCheck_sound and their frontier-open claims must be
 * checked against the exact Lean audit.
 *
 * Search domain:
 *   at most 3 assigned transition inputs;
 *   at most 10 successful blank-root moves;
 *   entry length <= 4 and positive macro period <= 6;
 *   ordinary actions only (24 nonhalting actions).
 */

const MAX_SLOTS = 3;
const MAX_STEPS = 10;
const MAX_ENTRY = 4;
const MAX_PERIOD = 6;
const ORACLE_BOUND = 6;
const ORACLE_RAY_LIMIT = 6;
const ORACLE_LASSO_LIMIT = 12;
const ORACLE_ENTRY_LIMIT = 2;
const ORACLE_MACRO_LIMIT = 4;
const PHYSICAL_SCAN_LIMIT = 12;

const blank = () => ({ state: 0, head: 0, ones: new Set() });
const slotIndex = (state, bit) => state * 2 + bit;
const readBit = c => c.ones.has(c.head) ? 1 : 0;
const decode = code => ({
  write: code >= 12,
  right: (code % 12) >= 6,
  next: code % 6
});
const actionName = code => {
  const a = decode(code);
  return `${a.write ? 1 : 0}${a.right ? "R" : "L"}${String.fromCharCode(65 + a.next)}`;
};
const slotName = slot =>
  `${String.fromCharCode(65 + Math.floor(slot / 2))}/${slot % 2}`;

function step(p, c) {
  const a = p.get(slotIndex(c.state, readBit(c)));
  if (a === undefined || a === null) return null;
  const ones = new Set(c.ones);
  if (a.write) ones.add(c.head);
  else ones.delete(c.head);
  return {
    state: a.next,
    head: c.head + (a.right ? 1 : -1),
    ones
  };
}

function run(p, c, n) {
  let d = c;
  for (let i = 0; i < n; i++) {
    d = step(p, d);
    if (d === null) return null;
  }
  return d;
}

function exactEq(a, b) {
  return !!a && !!b &&
    a.state === b.state &&
    a.head === b.head &&
    a.ones.size === b.ones.size &&
    [...a.ones].every(x => b.ones.has(x));
}

function shiftedEq(a, b, allowZero = false) {
  if (!a || !b || a.state !== b.state) return false;
  const delta = b.head - a.head;
  if (!allowZero && delta === 0) return false;
  if (a.ones.size !== b.ones.size) return false;
  return [...a.ones].every(x => b.ones.has(x + delta)) &&
    [...b.ones].every(y => a.ones.has(y - delta));
}

function finiteFreshRight(c) {
  return [...c.ones].every(x => x < c.head);
}
function finiteFreshLeft(c) {
  return [...c.ones].every(x => c.head < x);
}

/* Exact finiteRayCheck / finiteRayOracle mirror. */
function finiteRayOracle(p, maxSteps) {
  for (let n = 0; n <= maxSteps; n++) {
    const c = run(p, blank(), n);
    if (!c) continue;
    for (let mask = 0; mask < 64; mask++) {
      if (!(mask & (1 << c.state))) continue;
      for (const direction of [false, true]) {
        const fresh = direction ? finiteFreshRight(c) : finiteFreshLeft(c);
        if (!fresh) continue;
        let closed = true;
        for (let s = 0; s < 6; s++) {
          if (!(mask & (1 << s))) continue;
          const a = p.get(slotIndex(s, 0));
          if (!a || a.right !== direction || !(mask & (1 << a.next))) {
            closed = false;
            break;
          }
        }
        if (closed) return true;
      }
    }
  }
  return false;
}

/* Exact zeroMaskOracle mirror. */
function zeroMaskOracle(p) {
  for (let mask = 1; mask < 64; mask++) {
    if (!(mask & 1)) continue;
    let good = true;
    for (let s = 0; s < 6; s++) {
      if (!(mask & (1 << s))) continue;
      const a = p.get(slotIndex(s, 0));
      if (!a || a.write || !(mask & (1 << a.next))) {
        good = false;
        break;
      }
    }
    if (good) return true;
  }
  return false;
}

/* Exact finiteLassoOracle mirror. */
function finiteLassoOracle(p, maxSteps) {
  const configs = [blank()];
  for (let n = 1; n <= maxSteps; n++) {
    const c = step(p, configs[n - 1]);
    if (!c) break;
    configs.push(c);
    for (let k = 0; k < n; k++) {
      if (exactEq(c, configs[k])) return true;
    }
  }
  return false;
}

/* Exact finiteEntryMacroBiOracle mirror. */
function finiteEntryMacroBiOracle(p, entryLimit, macroLimit) {
  for (let k = 0; k < entryLimit; k++) {
    const entry = run(p, blank(), k);
    if (!entry) continue;
    for (let n = 1; n <= macroLimit; n++) {
      const start = { state: entry.state, head: 0, ones: new Set() };
      const configs = [start];
      let end = start;
      for (let j = 0; j < n; j++) {
        end = step(p, end);
        if (!end) break;
        configs.push(end);
      }
      if (configs.length !== n + 1) continue;
      const window = configs.slice(0, n);
      if (finiteFreshRight(entry) &&
          end.state === entry.state &&
          end.head > 0 &&
          finiteFreshRight(end) &&
          window.every(c => c.head >= 0)) return true;
      if (finiteFreshLeft(entry) &&
          end.state === entry.state &&
          end.head < 0 &&
          finiteFreshLeft(end) &&
          window.every(c => c.head <= 0)) return true;
    }
  }
  return false;
}

/* Exact lassoDecisionOracle disjuncts used by depth4ResidualAudit. */
function oldCombinedOracle(p) {
  // All candidates use ordinary actions only, so finiteHaltOracle is false.
  return finiteRayOracle(p, ORACLE_RAY_LIMIT) ||
    zeroMaskOracle(p) ||
    finiteLassoOracle(p, ORACLE_LASSO_LIMIT) ||
    finiteEntryMacroBiOracle(p, ORACLE_ENTRY_LIMIT, ORACLE_MACRO_LIMIT);
}

function toMap(table) {
  const p = new Map();
  for (let slot = 0; slot < 12; slot++) {
    if (table[slot] >= 0) p.set(slot, decode(table[slot]));
  }
  return p;
}

function translatedWitness(p, entry, period) {
  const c = run(p, blank(), entry);
  if (!c) return false;
  const d = run(p, c, period);
  return shiftedEq(c, d, true);
}

function firstUnknownPhysical(p, scanLimit) {
  let c = blank();
  for (let n = 0; n < scanLimit; n++) {
    const slot = slotIndex(c.state, readBit(c));
    if (!p.has(slot)) return slot;
    c = step(p, c);
    if (!c) return slot;
  }
  return null;
}

function prefixAudit(p) {
  let c = blank();
  const order = [];
  const seen = new Set();
  for (let n = 0; n < PHYSICAL_SCAN_LIMIT; n++) {
    const slot = slotIndex(c.state, readBit(c));
    if (!p.has(slot)) break;
    if (!seen.has(slot)) {
      seen.add(slot);
      order.push(slot);
    }
    c = step(p, c);
    if (!c) break;
  }
  const prefixes = [];
  for (let n = 0; n <= order.length; n++) {
    const q = new Map(order.slice(0, n).map(s => [s, p.get(s)]));
    prefixes.push({
      assigned: n,
      oldOracle: oldCombinedOracle(q),
      firstUnknown: firstUnknownPhysical(q, PHYSICAL_SCAN_LIMIT)
    });
  }
  return {
    firstUnknownOrder: order.map(slotName),
    fullScanNoUnknown: firstUnknownPhysical(p, PHYSICAL_SCAN_LIMIT) === null,
    prefixes
  };
}

/* A partial-table conflict means the two cylinders have no common completion. */
function tablesConflict(a, b) {
  for (let s = 0; s < 12; s++) {
    if (a[s] >= 0 && b[s] >= 0 && a[s] !== b[s]) return true;
  }
  return false;
}

const table = Array(12).fill(-1);
const found = new Map();
let nodes = 0;

function tableKey(t) {
  return t.map((x, i) => x < 0 ? "_" : `${i}:${x}`)
    .filter(x => x !== "_").join("|");
}

function dfs(c, steps, freshSlots, configs, path) {
  nodes++;

  if (steps > 0) {
    const lo = Math.max(0, steps - MAX_PERIOD);
    const hi = Math.min(MAX_ENTRY, steps - 1);
    for (let entry = lo; entry <= hi; entry++) {
      if (shiftedEq(configs[entry], c, false)) {
        const key = tableKey(table);
        if (!found.has(key)) {
          found.set(key, {
            table: table.slice(),
            entry,
            period: steps - entry,
            displacement: c.head - configs[entry].head,
            path: path.slice(),
            fixedSlots: table.filter(x => x >= 0).length
          });
        }
        return;
      }
    }
  }

  if (steps >= MAX_STEPS) return;
  const slot = slotIndex(c.state, readBit(c));
  const existing = table[slot];

  const follow = (actionCode, nextFreshSlots) => {
    const a = decode(actionCode);
    const ones = new Set(c.ones);
    if (a.write) ones.add(c.head);
    else ones.delete(c.head);
    const next = {
      state: a.next,
      head: c.head + (a.right ? 1 : -1),
      ones
    };
    dfs(next, steps + 1, nextFreshSlots, [...configs, next],
      [...path, actionCode]);
  };

  if (existing >= 0) {
    follow(existing, freshSlots);
    return;
  }
  if (freshSlots >= MAX_SLOTS) return;

  for (let action = 0; action < 24; action++) {
    table[slot] = action;
    follow(action, freshSlots + 1);
    table[slot] = -1;
  }
}

dfs(blank(), 0, 0, [blank()], []);

const all = [...found.values()];
const open = all.filter(candidate => {
  const p = toMap(candidate.table);
  return !oldCombinedOracle(p) &&
    translatedWitness(p, candidate.entry, candidate.period) &&
    firstUnknownPhysical(p, PHYSICAL_SCAN_LIMIT) === null;
});

const candidates = open.map(candidate => {
  const p = toMap(candidate.table);
  const audit = prefixAudit(p);
  return {
    entry: candidate.entry,
    period: candidate.period,
    displacement: candidate.displacement,
    fixedSlots: candidate.fixedSlots,
    transitions: candidate.table.flatMap((code, slot) =>
      code < 0 ? [] : [{
        slot: slotName(slot),
        action: actionName(code),
        code
      }]),
    path: candidate.path.map(actionName),
    ...audit
  };
});

let compatiblePairs = 0;
let conflictingPairs = 0;
for (let i = 0; i < open.length; i++) {
  for (let j = i + 1; j < open.length; j++) {
    if (tablesConflict(open[i].table, open[j].table)) conflictingPairs++;
    else compatiblePairs++;
  }
}

const summary = {
  search: {
    maxAssignedSlots: MAX_SLOTS,
    maxSuccessfulSteps: MAX_STEPS,
    maxEntry: MAX_ENTRY,
    maxPeriod: MAX_PERIOD,
    visitedNodes: nodes,
    translatedCandidates: all.length,
    translatedCandidateHistogram: all.reduce((h, c) => {
      h[c.fixedSlots] = (h[c.fixedSlots] || 0) + 1;
      return h;
    }, {})
  },
  openFamily: {
    count: candidates.length,
    allHaveExactlyThreeSlots: candidates.every(c => c.fixedSlots === 3),
    everyPrefixOldOracleFalse: candidates.every(c =>
      c.prefixes.length === 4 && c.prefixes.every(p => !p.oldOracle)),
    everyPrefixHasExpectedFirstUnknown: candidates.every(c =>
      c.prefixes.slice(0, 3).every((p, i) =>
        p.firstUnknown === c.firstUnknownOrder[i]) &&
      c.prefixes[3].firstUnknown === null),
    everyFullScanHasNoUnknown: candidates.every(c => c.fullScanNoUnknown),
    compatiblePairs,
    conflictingPairs,
    cylinderMassEach: "25^9 = 3814697265625",
    disjointUnionMass: "305175781250000",
    fractionOfAllTables: "0.512%"
  }
};

if (summary.openFamily.count !== 80 ||
    compatiblePairs !== 0 ||
    conflictingPairs !== 3160 ||
    !summary.openFamily.everyPrefixOldOracleFalse ||
    !summary.openFamily.everyPrefixHasExpectedFirstUnknown ||
    !summary.openFamily.everyFullScanHasNoUnknown) {
  throw new Error("translated-family audit failed; inspect the generated data");
}

console.log(JSON.stringify({ summary, candidates }, null, 2));
