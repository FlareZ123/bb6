#!/usr/bin/env node
"use strict";

// Source-faithful finite-trace product for the exact S-indexed correction-only
// window B_corr = 34*ell(S) + 122. Run from repository root:
//   node im-results/agent1-623-bcorr-event-product/analyze_bcorr_event_product.js
//
// This is a computational diagnostic, not an all-time theorem or BB(6) proof.

const fs = require("node:fs");
const path = require("node:path");
const root = process.cwd();
const read = (p) => JSON.parse(fs.readFileSync(path.join(root, p), "utf8"));

const resetDFA = read("im-results/agent32-623-phase-automaton/ResetPatternDFA.json");
const subsetDFA = read("im-results/agent27-623-root-scan/PairCarrySynchronizingSubsetDFA.json");
const postRoot = read("im-results/agent49-parity623/ResetPostStateDFA.json");
const postDFA = postRoot.post_reset_pair_and_length;
const closure = read("im-results/agent49-parity623/PostResetCarryPairClosure.json");
const bufferRoot = read("im-results/agent48-623-tight-window/ResetPostStateDFA_BufferRelative.json");
const bufferDFA = bufferRoot.pair_carry_and_length;

const resetAccepting = new Set(resetDFA.accepting_states);
const seedByTriple = new Map(
  closure.states.map((s) => [
    [s.L_state, s.R_state, s.previous_pair.join(",")].join("|"),
    s.id,
  ])
);

function evalA(a, k, m) {
  while (true) {
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
    const next = evalA(a, b - 1n, d + 2n * b + 3n);
    if (next === null || next[1] >= b) return null;
    [a, b, d] = next;
  }
  return [a, d];
}

function highLevelNext(a, d) {
  if (a === 0n) return d % 2n === 1n ? drainB(d + 1n, 2n, 2n) : [d, 7n];
  if (d % 2n === 1n && a >= d + 5n) return drainB(a - d - 5n, d + 3n, 5n);
  if (d % 2n === 0n && a >= d + 3n) return drainB(a - d - 2n, d + 2n, 2n);
  if (a % 2n === 1n) return null;
  if (a === d + 2n) return drainB(0n, a, 2n);
  if (d % 2n === 1n) return drainB(d + 4n - a, a - 1n, 3n);
  const p = evalA(d + 1n - a, a, 2n * a + 5n);
  return p === null ? null : drainB(...p);
}

function sectorData(a, d) {
  let q, p, sector;
  if (a >= d) {
    q = d;
    p = a - d;
    sector = d % 2n === 1n ? "LO" : "LE";
  } else {
    q = a;
    p = d - a;
    sector = d % 2n === 1n ? "RO" : "RE";
  }
  const g = p - 3n * q;
  const gamma = { LO: 18n, LE: 10n, RO: 2n, RE: 4n }[sector];
  return { q, S: a + d, g, gamma, x: 2n * g - gamma, y: 6n * q, sector };
}

function ellOf(v) {
  let ell = 0;
  let power = 1n;
  while ((power - 1n) / 2n < v + 3n) {
    ell += 1;
    power *= 3n;
  }
  return ell;
}

function floorDiv(a, b) {
  let q = a / b;
  const r = a % b;
  if (r !== 0n && a < 0n) q -= 1n;
  return q;
}

function mod(a, b) {
  let r = a % b;
  if (r < 0n) r += b;
  return r;
}

function pow3(k) {
  return 3n ** BigInt(k);
}

function windowIndices(B) {
  let k = 0;
  let p = 1;
  while (p <= B) {
    p *= 3;
    k += 1;
  }
  let j = 0;
  let p3 = 1n;
  const target = BigInt(B) ** 3n;
  while (p3 <= target) {
    p3 *= 3n;
    j += 1;
  }
  return { k, j };
}

function digitAt(x, i) {
  return Number(mod(floorDiv(x, pow3(i)), 3n));
}

function drainStats(b) {
  const value = 2n * b - 1n;
  let L = b % 2n === 1n ? 1 : 2;
  let p = pow3(L + 1);
  while (p <= value) {
    L += 2;
    p *= 9n;
  }
  const N = (value + pow3(L)) / 4n;
  let z = N;
  let n1 = 0;
  let n2 = 0;
  while (z > 0n) {
    const digit = z % 3n;
    if (digit === 1n) n1 += 1;
    if (digit === 2n) n2 += 1;
    z /= 3n;
  }
  return { L, N, n1, n2, D: L - 2 * n2, R: n1 + n2 };
}

const correctionConstants = {
  "LO/L": [-122n, 84n], "LE/L": [-68n, 48n],
  "RO/L": [0n, 0n], "RE/L": [-36n, 18n],
  "LO/R": [-6n, 24n], "LE/R": [-12n, 18n],
  "RO/R": [-44n, 30n], "RE/R": [-20n, 18n],
};

function corrections(sector, branch, stats) {
  const [cC, cF] = correctionConstants[sector + "/" + branch];
  if (branch === "L") {
    return {
      C: -18n * BigInt(stats.L) - 16n * BigInt(stats.n1) + 20n * BigInt(stats.n2) + cC,
      F: 12n * BigInt(stats.L) + 12n * BigInt(stats.n1) - 12n * BigInt(stats.n2) + cF,
    };
  }
  return {
    C: 12n * BigInt(stats.L) + 4n * BigInt(stats.n1) - 20n * BigInt(stats.n2) + cC,
    F: -6n * BigInt(stats.L) + 12n * BigInt(stats.n2) + cF,
  };
}

function sourceCarry(source, branch, C, F, k) {
  const K = pow3(k);
  const K1 = pow3(k + 1);
  const xK1 = mod(source.x, K1);
  const xK = mod(source.x, K);
  const yK = mod(source.y, K);
  if (branch === "L") {
    return [
      floorDiv(xK1 - 3n * yK + C, K1),
      floorDiv(3n * yK + F, K1),
    ];
  }
  return [
    floorDiv(-xK1 - 3n * xK - 3n * yK + C, K1),
    floorDiv(3n * xK + 3n * yK + F, K1),
  ];
}

function windowForState(state) {
  const ell = ellOf(state.S);
  const B = 34 * ell + 122;
  const { k, j } = windowIndices(B);
  return { ell, B, k, j, r: j - 3 * k };
}

function phaseForTransition(source, target) {
  const sourceWindow = windowForState(source);
  const targetWindow = windowForState(target);
  const branch = source.g > 0n ? "L" : "R";
  const drainInput = source.q + ({ LO: 3n, LE: 2n, RO: -1n, RE: 1n }[source.sector]);
  const stats = drainStats(drainInput);
  const { C, F } = corrections(source.sector, branch, stats);
  const T = 3n * BigInt(stats.D) + 2n * BigInt(stats.R) +
    ({ LO: 19n, LE: 10n, RO: -4n, RE: 2n }[source.sector]);
  const branchByThreshold = source.g >= T ? "L" : "R";

  let carry = sourceCarry(source, branch, C, F, sourceWindow.k);
  let prev = [digitAt(source.x, sourceWindow.k), digitAt(source.y, sourceWindow.k)];
  for (let i = sourceWindow.k + 1; i <= targetWindow.k + 1; i += 1) {
    const xi = BigInt(digitAt(source.x, i));
    const yi = BigInt(digitAt(source.y, i));
    let tx, ty;
    if (branch === "L") {
      tx = xi - BigInt(prev[1]) + carry[0];
      ty = BigInt(prev[1]) + carry[1];
    } else {
      tx = -xi - BigInt(prev[0]) - BigInt(prev[1]) + carry[0];
      ty = BigInt(prev[0]) + BigInt(prev[1]) + carry[1];
    }
    carry = [floorDiv(tx, 3n), floorDiv(ty, 3n)];
    prev = [Number(xi), Number(yi)];
  }

  const kShift = targetWindow.k - sourceWindow.k;
  const jShift = targetWindow.j - sourceWindow.j;
  if (![0, 1].includes(kShift) || ![0, 1].includes(jShift) || (kShift === 1 && jShift !== 1)) {
    throw new Error("S-window shift violates the coupled 0/1 bound");
  }
  if (![ -2, -1, 0 ].includes(sourceWindow.r) || ![ -2, -1, 0 ].includes(targetWindow.r)) {
    throw new Error("S-window boundary phase r is outside {-2,-1,0}");
  }

  return {
    key: [
      source.sector, branch, target.sector, target.g > 0n ? "L" : "R",
      prev.join(","), Number(carry[0]) + "," + Number(carry[1]),
      sourceWindow.r, targetWindow.r, kShift, jShift,
    ].join("|"),
    branchMismatch: branch !== branchByThreshold,
  };
}

function targetWord(state) {
  const w = windowForState(state);
  const word = [];
  for (let i = w.k + 2; i < w.j - 2; i += 1) {
    word.push(digitAt(state.x, i) * 3 + digitAt(state.y, i));
  }
  return { word, window: w };
}

function runBufferDFA(word) {
  let state = bufferDFA.initial_state;
  let rolling = [0, 0];
  let event = null;

  for (let i = 0; i < word.length; i += 1) {
    const symbol = word[i];
    const preState = state;
    rolling.push(symbol);
    if (rolling.length > 5) rolling.shift();
    state = bufferDFA.transitions[state][symbol];

    if (event === null && bufferDFA.outputs[state] !== null &&
        bufferDFA.outputs[state] !== undefined) {
      const label = bufferDFA.output_labels[bufferDFA.outputs[state]];
      const witnessLength = Number(label.key.split("|").at(-1));
      const second = rolling[6 - witnessLength];
      if (second === undefined) {
        throw new Error("Buffer-relative second witness symbol is unavailable");
      }
      event = { position: i, preState, symbol, second, witnessLength };
    }
  }

  if (event === null) throw new Error("Buffer-relative DFA did not find a reset event");
  return { state, event };
}

function summarize(records, keyOf) {
  const keys = records.map(keyOf);
  const distinct = new Set(keys).size;
  const nextByKey = new Map();

  for (let i = 0; i + 1 < keys.length; i += 1) {
    if (!nextByKey.has(keys[i])) nextByKey.set(keys[i], new Set());
    nextByKey.get(keys[i]).add(keys[i + 1]);
  }

  let branching = 0;
  let maxOutdegree = 0;
  const outdegreeHistogram = {};
  for (const successors of nextByKey.values()) {
    const degree = successors.size;
    outdegreeHistogram[degree] = (outdegreeHistogram[degree] || 0) + 1;
    if (degree > 1) branching += 1;
    maxOutdegree = Math.max(maxOutdegree, degree);
  }

  return {
    distinct,
    repeated: keys.length - distinct,
    branching,
    maxOutdegree,
    observedEdges: keys.length - 1,
    terminalRecords: 1,
    outdegreeHistogram,
  };
}

function histogram(values) {
  const h = {};
  for (const value of values) {
    const key = String(value);
    h[key] = (h[key] || 0) + 1;
  }
  return h;
}

const records = [];
let a = 0n;
let d = 7n;
let resetFailures = 0;
let postResetMismatches = 0;
let bufferEventMismatches = 0;
let missingSeeds = 0;
let finalOutsideSubset = 0;
let branchMismatches = 0;
let nonsynchronizing = 0;
const subsetSizeHistogram = {};

for (let n = 0; n <= 10000; n += 1) {
  const next = highLevelNext(a, d);
  if (next === null) throw new Error("Root recurrence stopped at D" + n);

  if (n >= 33) {
    const source = sectorData(a, d);
    const target = sectorData(next[0], next[1]);
    const phase = phaseForTransition(source, target);
    if (phase.branchMismatch) branchMismatches += 1;

    const { word, window } = targetWord(target);

    let resetState = resetDFA.initial_state;
    let firstResetEnd = -1;
    for (let i = 0; i < word.length; i += 1) {
      resetState = resetDFA.transitions[resetState][word[i]];
      if (firstResetEnd < 0 && resetAccepting.has(resetState)) firstResetEnd = i + 1;
    }
    if (firstResetEnd < 0) {
      resetFailures += 1;
      [a, d] = next;
      continue;
    }

    let postState = postDFA.initial_state;
    let postFirstEnd = -1;
    for (let i = 0; i < word.length; i += 1) {
      postState = postDFA.transitions[postState][word[i]];
      if (postFirstEnd < 0 && postDFA.outputs[postState] !== null &&
          postDFA.outputs[postState] !== undefined) {
        postFirstEnd = i + 1;
      }
    }
    if (postFirstEnd !== firstResetEnd) postResetMismatches += 1;

    const outputLabel = postDFA.output_labels[postDFA.outputs[postState]];
    const seedKey = [
      outputLabel.L_final_state,
      outputLabel.R_final_state,
      outputLabel.L_final.previous_pair.join(","),
    ].join("|");
    let finalCarry = seedByTriple.get(seedKey);
    if (finalCarry === undefined) {
      missingSeeds += 1;
    } else {
      for (let i = firstResetEnd; i < word.length; i += 1) {
        finalCarry = closure.transitions[finalCarry][word[i]];
      }
    }

    let subsetState = subsetDFA.initial_state;
    for (let i = firstResetEnd; i < word.length; i += 1) {
      subsetState = subsetDFA.image_subset_transitions[subsetState][word[i]];
    }
    const image = subsetDFA.image_subset_states[subsetState];
    if (image.length > 1) nonsynchronizing += 1;
    subsetSizeHistogram[image.length] = (subsetSizeHistogram[image.length] || 0) + 1;
    if (finalCarry !== undefined && !image.includes(finalCarry)) finalOutsideSubset += 1;

    const buffer = runBufferDFA(word);
    if (buffer.event.position + 1 !== firstResetEnd) bufferEventMismatches += 1;

    const productKey = [
      phase.key,
      finalCarry,
      buffer.event.position,
      buffer.event.preState,
      buffer.event.symbol,
      buffer.event.second,
    ].join("|");

    records.push({
      n,
      targetIndex: n + 1,
      phase: phase.key,
      finalCarry,
      seed: seedKey,
      subsetState,
      subsetSize: image.length,
      bufferState: buffer.state,
      event: buffer.event,
      productKey,
      firstResetEnd,
      windowLength: word.length,
      windowEll: window.ell,
      windowR: window.r,
    });
  }

  [a, d] = next;
}

if (resetFailures || postResetMismatches || bufferEventMismatches ||
    missingSeeds || finalOutsideSubset || branchMismatches) {
  throw new Error(JSON.stringify({
    resetFailures, postResetMismatches, bufferEventMismatches,
    missingSeeds, finalOutsideSubset, branchMismatches,
  }));
}

const ablations = {
  outputStateOnly: summarize(records, (r) =>
    [r.phase, r.finalCarry, r.bufferState].join("|")),
  outputStatePlusEventPosition: summarize(records, (r) =>
    [r.phase, r.finalCarry, r.bufferState, r.event.position].join("|")),
  outputStatePlusPreOutputState: summarize(records, (r) =>
    [r.phase, r.finalCarry, r.bufferState, r.event.preState].join("|")),
  outputStatePlusCurrentSymbol: summarize(records, (r) =>
    [r.phase, r.finalCarry, r.bufferState, r.event.symbol].join("|")),
  outputStatePlusSecondWitnessSymbol: summarize(records, (r) =>
    [r.phase, r.finalCarry, r.bufferState, r.event.second].join("|")),
  outputStatePlusPreSymbolSecond: summarize(records, (r) =>
    [r.phase, r.finalCarry, r.bufferState, r.event.preState,
      r.event.symbol, r.event.second].join("|")),
  outputStatePlusPositionPreSymbolSecond: summarize(records, (r) =>
    [r.phase, r.finalCarry, r.bufferState, r.event.position,
      r.event.preState, r.event.symbol, r.event.second].join("|")),
};

const compactProduct = summarize(records, (r) => r.productKey);
const report = {
  method: {
    window: "B_corr = 34*ell_S + 122",
    phase: "Agent48 source-to-target S-window phase, including low-boundary advance",
    bufferDFA: "580-state pair_carry_and_length buffer-relative DFA",
    product: "(phase, exact final 66-state carry, first-output position, pre-output state, current symbol, second witness symbol)",
    range: "D33->D34 through D10000->D10001",
  },
  counts: {
    transitions: records.length,
    distinctPhases: new Set(records.map((r) => r.phase)).size,
    distinctUniversalSubsetStates: new Set(records.map((r) => r.subsetState)).size,
    nonsynchronizingSuffixes: nonsynchronizing,
    subsetSizeHistogram,
    distinctResetSeeds: new Set(records.map((r) => r.seed)).size,
    distinctFinalCarryStates: new Set(records.map((r) => r.finalCarry)).size,
    distinctBufferOutputStates: new Set(records.map((r) => r.bufferState)).size,
    distinctPreOutputStates: new Set(records.map((r) => r.event.preState)).size,
    eventPositionHistogram: histogram(records.map((r) => r.event.position)),
    witnessLengthHistogram: histogram(records.map((r) => r.event.witnessLength)),
    firstResetEndHistogram: histogram(records.map((r) => r.firstResetEnd)),
    branchMismatches,
    resetFailures,
    postResetMismatches,
    bufferEventMismatches,
    missingSeeds,
    finalOutsideSubset,
  },
  compactProduct,
  ablations,
  samples: {
    first: records.slice(0, 3),
    last: records.slice(-3),
  },
};

const outputPath = path.join(
  root,
  "im-results/agent1-623-bcorr-event-product/SourceFaithfulBcorrEventProduct.json"
);
fs.writeFileSync(outputPath, JSON.stringify(report, null, 2) + "\n");
process.stdout.write(JSON.stringify({
  outputPath: path.relative(root, outputPath),
  counts: report.counts,
  compactProduct: report.compactProduct,
  ablations: report.ablations,
}, null, 2) + "\n");
