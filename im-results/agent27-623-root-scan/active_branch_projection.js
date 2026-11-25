#!/usr/bin/env node
"use strict";

// Exact-seed / active-branch projection audit for the #623 S-window suffixes.
// Run from the repository root: node im-results/agent27-623-root-scan/active_branch_projection.js

const fs = require("node:fs");
const path = require("node:path");
const read = (p) => JSON.parse(fs.readFileSync(path.join(process.cwd(), p), "utf8"));

const reset = read("im-results/agent32-623-phase-automaton/ResetPatternDFA.json");
const subset = read("im-results/agent27-623-root-scan/PairCarrySynchronizingSubsetDFA.json");
const post = read("im-results/agent49-parity623/ResetPostStateDFA.json").post_reset_pair_and_length;
const closure = read("im-results/agent49-parity623/PostResetCarryPairClosure.json");
const edges = read("im-results/agent48-623-tight-window/SWindowEdgeRecords.json");
const scc = read("im-results/agent27-623-root-scan/NonSynchronizingSCCs.json");

const accepting = new Set(reset.accepting_states);
const seedByKey = new Map(closure.states.map((s) => [
  [s.L_state, s.R_state, s.previous_pair.join(",")].join("|"), s.id
]));
const rowByTarget = new Map(edges.edges.map((r) => [r[0], r]));
const phaseById = new Map(edges.phaseRecords.map(([id, _key, phase]) => [id, phase]));
const componentByState = new Map();
for (const component of scc.scc_partition.recurrent_nonsingleton_components_detail) {
  for (const state of component.states) componentByState.set(state.id, component.label);
}

function floorDiv(a, b) {
  let q = a / b;
  if (a % b !== 0n && a < 0n) q -= 1n;
  return q;
}

function evalA(a, k, m) {
  for (;;) {
    if (k % 3n === 2n) return [a + 1n, k / 3n, m];
    if (a === 0n) return k % 3n === 0n ? null : [0n, k / 3n, m];
    if (k % 3n === 0n) return [a - 1n, k / 3n, m + 2n];
    k /= 3n;
    m += 2n * k + 3n;
    a -= 1n;
  }
}

function drainB(a, b, d) {
  while (b !== 0n) {
    const z = evalA(a, b - 1n, d + 2n * b + 3n);
    if (z === null || z[1] >= b) return null;
    [a, b, d] = z;
  }
  return [a, d];
}

function next(a, d) {
  if (a === 0n) return d % 2n === 1n ? drainB(d + 1n, 2n, 2n) : [d, 7n];
  if (d % 2n === 1n && a >= d + 5n) return drainB(a - d - 5n, d + 3n, 5n);
  if (d % 2n === 0n && a >= d + 3n) return drainB(a - d - 2n, d + 2n, 2n);
  if (a % 2n === 1n) return null;
  if (a === d + 2n) return drainB(0n, a, 2n);
  if (d % 2n === 1n) return drainB(d + 4n - a, a - 1n, 3n);
  const z = evalA(d + 1n - a, a, 2n * a + 5n);
  return z === null ? null : drainB(...z);
}

function sector(a, d) {
  let q, p, name;
  if (a >= d) {
    q = d;
    p = a - d;
    name = d % 2n === 1n ? "LO" : "LE";
  } else {
    q = a;
    p = d - a;
    name = d % 2n === 1n ? "RO" : "RE";
  }
  const gamma = { LO: 18n, LE: 10n, RO: 2n, RE: 4n }[name];
  const g = p - 3n * q;
  return { q, p, S: a + d, g, sector: name, x: 2n * g - gamma, y: 6n * q };
}

function ellOf(S) {
  let ell = 0;
  let p = 1n;
  while ((p - 1n) / 2n < S + 3n) {
    ell += 1;
    p *= 3n;
  }
  return ell;
}

function windowForState(s) {
  const B = 34n * BigInt(ellOf(s.S)) + 122n;
  let k = 0;
  let p = 1n;
  while (p <= B) {
    k += 1;
    p *= 3n;
  }
  let j = 0;
  let p3 = 1n;
  while (p3 <= B ** 3n) {
    j += 1;
    p3 *= 3n;
  }
  return { k, j };
}

function digitAt(x, i) {
  const q = floorDiv(x, 3n ** BigInt(i));
  const r = q % 3n;
  return Number(r < 0n ? r + 3n : r);
}

function targetWord(s, w) {
  const out = [];
  for (let i = w.k + 2; i < w.j - 2; i += 1) {
    out.push(3 * digitAt(s.x, i) + digitAt(s.y, i));
  }
  return out;
}

let totals = {
  windows: 0,
  resetFailures: 0,
  missingPostResetSeed: 0,
  exactCarryOutsideUniversalImage: 0,
  nonsingletonSuffixes: 0,
  activeProjectionSingleton: 0
};
const componentCounts = {};
const activeProjectionSizeHistogram = {};
const ambiguous = [];

let a = 0n;
let d = 7n;
for (let n = 0; n <= 10000; n += 1) {
  if (n >= 34 && n <= 10000) {
    const s = sector(a, d);
    const word = targetWord(s, windowForState(s));

    let resetState = reset.initial_state;
    let firstResetEnd = -1;
    for (let i = 0; i < word.length; i += 1) {
      resetState = reset.transitions[resetState][word[i]];
      if (firstResetEnd < 0 && accepting.has(resetState)) firstResetEnd = i + 1;
    }
    if (firstResetEnd < 0) {
      totals.resetFailures += 1;
    } else {
      let postState = post.initial_state;
      for (const symbol of word) postState = post.transitions[postState][symbol];
      const outputIndex = post.outputs[postState];
      const label = outputIndex === null || outputIndex === undefined
        ? null : post.output_labels[outputIndex];

      if (label === null) {
        totals.missingPostResetSeed += 1;
      } else {
        const seedKey = [
          label.L_final_state,
          label.R_final_state,
          label.L_final.previous_pair.join(",")
        ].join("|");
        let exactFinalCarry = seedByKey.get(seedKey);

        if (exactFinalCarry === undefined) {
          totals.missingPostResetSeed += 1;
        } else {
          let subsetState = subset.initial_state;
          for (let i = firstResetEnd; i < word.length; i += 1) {
            exactFinalCarry = closure.transitions[exactFinalCarry][word[i]];
            subsetState = subset.image_subset_transitions[subsetState][word[i]];
          }

          const image = subset.image_subset_states[subsetState];
          if (!image.includes(exactFinalCarry)) {
            totals.exactCarryOutsideUniversalImage += 1;
          }

          if (image.length > 1) {
            totals.nonsingletonSuffixes += 1;

            // The active branch belongs to this state's own outgoing edge:
            // D_n -> D_(n+1), whose edge record is keyed by targetIndex n+1.
            const edge = rowByTarget.get(n + 1);
            if (!edge) throw new Error(`missing outgoing edge record for D_${n}`);
            const phase = phaseById.get(edge[1]);
            if (!phase) throw new Error(`missing phase record ${edge[1]}`);
            const branch = phase[1];

            const activeStates = [...new Set(image.map((id) =>
              branch === "L" ? closure.states[id].L_state : closure.states[id].R_state
            ))].sort((x, y) => x - y);
            const actualActiveState = branch === "L"
              ? closure.states[exactFinalCarry].L_state
              : closure.states[exactFinalCarry].R_state;
            const component = componentByState.get(subsetState) || "transient";

            componentCounts[component] ||= {
              count: 0, activeProjectionSingleton: 0, activeProjectionAmbiguous: 0
            };
            componentCounts[component].count += 1;
            activeProjectionSizeHistogram[activeStates.length] =
              (activeProjectionSizeHistogram[activeStates.length] || 0) + 1;

            if (activeStates.length === 1) {
              totals.activeProjectionSingleton += 1;
              componentCounts[component].activeProjectionSingleton += 1;
            } else {
              componentCounts[component].activeProjectionAmbiguous += 1;
              ambiguous.push({
                stateIndex: n,
                branch,
                subsetState,
                component,
                subsetSize: image.length,
                activeStates,
                actualActiveState,
                actualIncluded: activeStates.includes(actualActiveState)
              });
            }
          }
        }
      }
    }
    totals.windows += 1;
  }

  const z = next(a, d);
  if (z === null) throw new Error(`root halts at index ${n}`);
  [a, d] = z;
}

const summary = {
  scope: "D34 through D10000 inclusive; outgoing branch from the exact SWindowEdgeRecords phase",
  totals,
  activeProjectionAmbiguous: totals.nonsingletonSuffixes - totals.activeProjectionSingleton,
  componentCounts,
  activeProjectionSizeHistogram,
  ambiguousStateIndices: ambiguous.map((r) => r.stateIndex),
  ambiguous
};

if (totals.windows !== 9967 ||
    totals.resetFailures !== 0 ||
    totals.missingPostResetSeed !== 0 ||
    totals.exactCarryOutsideUniversalImage !== 0 ||
    totals.nonsingletonSuffixes !== 84 ||
    totals.activeProjectionSingleton !== 21) {
  throw new Error("audit totals differ from the recorded expected counts: " + JSON.stringify(summary));
}

process.stdout.write(JSON.stringify(summary, null, 2) + "\n");
