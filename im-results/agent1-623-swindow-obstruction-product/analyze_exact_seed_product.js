/*
 * RETRACTED FOR SOURCE-FAITHFUL S-WINDOW ANALYSIS.
 * This reproduces a superseded conservative buffer B_S=max(34*ell+140,36*ell+88)
 * and an own-start phase diagnostic. It does not implement the exact
 * B_corr=34*ell+122 source-to-target phase. See
 * im-results/agent1-623-bcorr-event-product/README.md.
 * Kept only to reproduce the historical conservative diagnostic.
 */
#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");
const root = process.cwd();

function readJson(relativePath) {
  return JSON.parse(fs.readFileSync(path.join(root, relativePath), "utf8"));
}

const resetDFA = readJson("im-results/agent32-623-phase-automaton/ResetPatternDFA.json");
const subsetDFA = readJson("im-results/agent27-623-root-scan/PairCarrySynchronizingSubsetDFA.json");
const sccData = readJson("im-results/agent27-623-root-scan/NonSynchronizingSCCs.json");
const postResetData = readJson("im-results/agent49-parity623/ResetPostStateDFA.json");
const closure = readJson("im-results/agent49-parity623/PostResetCarryPairClosure.json");
const postResetPairLength = postResetData.post_reset_pair_and_length;

const accepting = new Set(resetDFA.accepting_states);
const componentOf = new Map();
for (const component of sccData.scc_partition.recurrent_nonsingleton_components_detail) {
  for (const state of component.states) componentOf.set(state.id, component.label);
}
const seedStateOf = new Map();
for (const state of closure.states) {
  const key = state.L_state + "|" + state.R_state + "|" + state.previous_pair.join(",");
  seedStateOf.set(key, state.id);
}

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
  return { q, S: a + d, g, x: 2n * g - gamma, y: 6n * q, sector };
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

function windowForState(state) {
  const ell = ellOf(state.S);
  const buffer = Math.max(34 * ell + 140, 36 * ell + 88);
  const { k, j } = windowIndices(buffer);
  return { ell, buffer, k, j, r: j - 3 * k, length: j - k - 4 };
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
  return { L, n1, n2, D: L - 2 * n2, R: n1 + n2 };
}

const correctionConstants = {
  "LO/L": [-122n, 84n], "LE/L": [-68n, 48n],
  "RO/L": [0n, 0n], "RE/L": [-36n, 18n],
  "LO/R": [-6n, 24n], "LE/R": [-12n, 18n],
  "RO/R": [-44n, 30n], "RE/R": [-20n, 18n]
};

function corrections(sector, branch, stats) {
  const [cC, cF] = correctionConstants[sector + "/" + branch];
  if (branch === "L") {
    return {
      C: -18n * BigInt(stats.L) - 16n * BigInt(stats.n1) + 20n * BigInt(stats.n2) + cC,
      F: 12n * BigInt(stats.L) + 12n * BigInt(stats.n1) - 12n * BigInt(stats.n2) + cF
    };
  }
  return {
    C: 12n * BigInt(stats.L) + 4n * BigInt(stats.n1) - 20n * BigInt(stats.n2) + cC,
    F: -6n * BigInt(stats.L) + 12n * BigInt(stats.n2) + cF
  };
}

function sourceCarry(state, branch, C, F, k) {
  const K = pow3(k);
  const K1 = pow3(k + 1);
  const xK1 = mod(state.x, K1);
  const xK = mod(state.x, K);
  const yK = mod(state.y, K);
  if (branch === "L") {
    return [
      floorDiv(xK1 - 3n * yK + C, K1),
      floorDiv(3n * yK + F, K1)
    ];
  }
  return [
    floorDiv(-xK1 - 3n * xK - 3n * yK + C, K1),
    floorDiv(3n * xK + 3n * yK + F, K1)
  ];
}

function advanceOne(state, branch, carry, previous, index) {
  const x = BigInt(digitAt(state.x, index));
  const y = BigInt(digitAt(state.y, index));
  const px = BigInt(previous[0]);
  const py = BigInt(previous[1]);
  const tx = branch === "L"
    ? x - py + carry[0]
    : -x - px - py + carry[0];
  const ty = branch === "L"
    ? py + carry[1]
    : px + py + carry[1];
  return {
    carry: [floorDiv(tx, 3n), floorDiv(ty, 3n)],
    previous: [Number(x), Number(y)]
  };
}

function analyzeState(state, index) {
  const window = windowForState(state);
  const word = [];
  for (let i = window.k + 2; i < window.j - 2; i++) {
    word.push(digitAt(state.x, i) * 3 + digitAt(state.y, i));
  }

  let resetState = resetDFA.initial_state;
  let firstResetEnd = -1;
  for (let i = 0; i < word.length; i++) {
    resetState = resetDFA.transitions[resetState][word[i]];
    if (firstResetEnd < 0 && accepting.has(resetState)) firstResetEnd = i + 1;
  }
  if (firstResetEnd < 0) throw new Error("No common reset at D" + index);

  let postState = postResetPairLength.initial_state;
  let postResetEnd = -1;
  for (let i = 0; i < word.length; i++) {
    postState = postResetPairLength.transitions[postState][word[i]];
    if (postResetEnd < 0 &&
        postResetPairLength.outputs[postState] !== null &&
        postResetPairLength.outputs[postState] !== undefined) {
      postResetEnd = i + 1;
    }
  }
  if (postResetEnd !== firstResetEnd) {
    throw new Error("Reset recognizers disagree at D" + index);
  }
  const outputIndex = postResetPairLength.outputs[postState];
  if (outputIndex === null || outputIndex === undefined) {
    throw new Error("Post-reset output missing at D" + index);
  }
  const label = postResetPairLength.output_labels[outputIndex];
  if (label.witness_length < 3 || label.witness_length > 6 ||
      firstResetEnd < label.witness_length) {
    throw new Error("Reset witness/label mismatch at D" + index);
  }

  const seedKey = label.L_final_state + "|" + label.R_final_state + "|" +
    label.L_final.previous_pair.join(",");
  const seedState = seedStateOf.get(seedKey);
  if (seedState === undefined) throw new Error("Reset label outside 66-state closure");

  let finalState = seedState;
  for (let i = firstResetEnd; i < word.length; i++) {
    finalState = closure.transitions[finalState][word[i]];
    if (finalState === undefined) throw new Error("Suffix leaves 66-state closure");
  }

  let subsetState = subsetDFA.initial_state;
  for (let i = firstResetEnd; i < word.length; i++) {
    subsetState = subsetDFA.image_subset_transitions[subsetState][word[i]];
  }
  const subsetMembers = subsetDFA.image_subset_states[subsetState];
  const actualInSubset = subsetMembers.includes(finalState);
  if (!actualInSubset) throw new Error("Exact seed run not contained in universal subset");

  const leftProjection = new Set(subsetMembers.map(id => closure.states[id].L_state)).size;
  const rightProjection = new Set(subsetMembers.map(id => closure.states[id].R_state)).size;

  const branch = state.g > 0n ? "L" : "R";
  const drainInput = state.q + ({ LO: 3n, LE: 2n, RO: -1n, RE: 1n }[state.sector]);
  const stats = drainStats(drainInput);
  const threshold = 3n * BigInt(stats.D) + 2n * BigInt(stats.R) +
    ({ LO: 19n, LE: 10n, RO: -4n, RE: 2n }[state.sector]);
  const branchByThreshold = state.g >= threshold ? "L" : "R";
  const { C, F } = corrections(state.sector, branch, stats);
  const initialCarry = sourceCarry(state, branch, C, F, window.k);
  const initialPrevious = [digitAt(state.x, window.k), digitAt(state.y, window.k)];
  const ownStep = advanceOne(state, branch, initialCarry, initialPrevious, window.k + 1);
  const ownStartKey = [
    state.sector,
    branch,
    ownStep.previous.join(","),
    ownStep.carry.map(String).join(","),
    window.r
  ].join("|");

  const resetWitness = word.slice(firstResetEnd - label.witness_length, firstResetEnd);
  if (resetWitness.length !== label.witness_length) {
    throw new Error("Reset witness length mismatch at D" + index);
  }
  const secondSymbol = resetWitness[1];
  const tail = word.slice(-5);

  return {
    index,
    S: state.S.toString(),
    ell: window.ell,
    k: window.k,
    j: window.j,
    r: window.r,
    windowLength: word.length,
    firstResetEnd,
    postResetEnd,
    suffixLength: word.length - firstResetEnd,
    resetLabelKey: label.key,
    witnessLength: label.witness_length,
    resetWitness: resetWitness.join(","),
    secondResetSymbol: secondSymbol,
    resetSeedState: seedState,
    finalCarryState: finalState,
    ownStartKey,
    subsetState,
    subsetSize: subsetMembers.length,
    component: componentOf.get(subsetState) || (subsetMembers.length === 1 ? "SYNC" : "TRANSIENT"),
    activeBranch: branch,
    activeProjectionCount: branch === "L" ? leftProjection : rightProjection,
    actualFinalStateInSubset: actualInSubset,
    tail5: tail.join(","),
    branchMismatch: branch !== branchByThreshold
  };
}

function productKey(record, kind) {
  if (kind === "ownSubset") return record.ownStartKey + "|" + record.subsetState;
  if (kind === "ownFinal") return record.ownStartKey + "|" + record.finalCarryState;
  if (kind === "ownFinalSeed") {
    return record.ownStartKey + "|" + record.finalCarryState + "|" + record.resetSeedState;
  }
  if (kind === "ownFinalSeedTail") {
    return record.ownStartKey + "|" + record.finalCarryState + "|" +
      record.resetSeedState + "|" + record.tail5;
  }
  throw new Error("Unknown product kind " + kind);
}

function productSummary(records, kind) {
  const successors = new Map();
  for (let i = 0; i < records.length; i++) {
    const key = productKey(records[i], kind);
    const nextKey = i + 1 < records.length ? productKey(records[i + 1], kind) : null;
    if (!successors.has(key)) successors.set(key, new Set());
    if (nextKey !== null) successors.get(key).add(nextKey);
  }
  const histogram = {};
  let branching = 0;
  let maxOutdegree = 0;
  for (const values of successors.values()) {
    const degree = values.size;
    histogram[degree] = (histogram[degree] || 0) + 1;
    if (degree > 1) branching += 1;
    if (degree > maxOutdegree) maxOutdegree = degree;
  }
  return {
    distinctStates: new Set(records.map(record => productKey(record, kind))).size,
    repeatedOccurrences: records.length -
      new Set(records.map(record => productKey(record, kind))).size,
    branchingStates: branching,
    maxOutdegree,
    outdegreeHistogram: histogram
  };
}

function exceptionSummary(records) {
  const exceptions = records.filter(record => record.subsetSize > 1);
  const distribution = {};
  for (const record of exceptions) {
    const projection = record.activeProjectionCount === 1
      ? "active-singleton" : "active-ambiguous";
    const key = record.component + "|" + record.activeBranch + "|" + projection;
    distribution[key] = (distribution[key] || 0) + 1;
  }
  return {
    count: exceptions.length,
    indices: exceptions.map(record => record.index),
    componentBranchProjectionDistribution: distribution
  };
}

function collision(records, kind, wantedKey) {
  const groups = new Map();
  for (let i = 0; i < records.length; i++) {
    const key = productKey(records[i], kind);
    if (wantedKey && key !== wantedKey) continue;
    if (!groups.has(key)) groups.set(key, []);
    groups.get(key).push({
      record: records[i],
      next: i + 1 < records.length ? productKey(records[i + 1], kind) : null
    });
  }
  for (const [key, occurrences] of groups) {
    const nextKeys = new Set(occurrences.map(item => item.next));
    if (occurrences.length > 1 && nextKeys.size > 1) {
      return {
        key,
        occurrences: occurrences.map(item => ({
          index: item.record.index,
          ell: item.record.ell,
          k: item.record.k,
          j: item.record.j,
          windowLength: item.record.windowLength,
          resetSeedState: item.record.resetSeedState,
          finalCarryState: item.record.finalCarryState,
          nextProductKey: item.next
        }))
      };
    }
  }
  return null;
}

const allRecords = [];
let a = 0n;
let d = 7n;
for (let index = 0; index <= 10001; index++) {
  if (index >= 33) allRecords.push(analyzeState(sectorData(a, d), index));
  if (index === 10001) break;
  const next = highLevelNext(a, d);
  if (next === null) throw new Error("Root recurrence stopped at index " + index);
  [a, d] = next;
}

const sourceRecords = allRecords.filter(record => record.index <= 10000);
const targetRecords = allRecords.filter(record => record.index >= 34 && record.index <= 10001);
if (sourceRecords.length !== 9968 || targetRecords.length !== 9968) {
  throw new Error("Unexpected source/target record count");
}

const sourceExceptions = exceptionSummary(sourceRecords);
const targetExceptions = exceptionSummary(targetRecords);
const firstResetHistogram = {};
for (const record of sourceRecords) {
  firstResetHistogram[record.firstResetEnd] =
    (firstResetHistogram[record.firstResetEnd] || 0) + 1;
}

const sourceProducts = {
  ownStartTimesUniversalSubset: productSummary(sourceRecords, "ownSubset"),
  ownStartTimesExactFinalCarry: productSummary(sourceRecords, "ownFinal"),
  ownStartTimesExactFinalCarryAndSeed: productSummary(sourceRecords, "ownFinalSeed"),
  ownStartTimesExactFinalCarrySeedAndTail5: productSummary(sourceRecords, "ownFinalSeedTail")
};

const result = {
  description: "Finite source-aligned conservative S-window replay for the authentic #623 root. The 211-subset state is a universal suffix-rank diagnostic; the reset-output label supplies the actual seed for the authentic carry.",
  scope: {
    rootStart: "D(0,7)",
    sourceStates: "D33 through D10000",
    targetStates: "D34 through D10001",
    transitions: 9968,
    buffer: "B_S=max(34*ell_S+140,36*ell_S+88)",
    window: "[k+2,j-2), where 3^k>B_S and 3^j>B_S^3"
  },
  sourceWindow: {
    count: sourceRecords.length,
    resetFailures: sourceRecords.filter(record => record.firstResetEnd < 0).length,
    firstResetEndHistogram: firstResetHistogram,
    ownStartPhaseKeys: new Set(sourceRecords.map(record => record.ownStartKey)).size,
    distinctSubsetStates: new Set(sourceRecords.map(record => record.subsetState)).size,
    nonsynchronizingSuffixes: sourceExceptions,
    exactFinalCarryStates: new Set(sourceRecords.map(record => record.finalCarryState)).size,
    exactSeedMissing: sourceRecords.filter(record => record.resetSeedState === undefined).length,
    exactFinalCarryOutsideUniversalSubset: sourceRecords.filter(record => !record.actualFinalStateInSubset).length,
    branchMismatches: sourceRecords.filter(record => record.branchMismatch).length
  },
  targetWindow: {
    count: targetRecords.length,
    resetFailures: targetRecords.filter(record => record.firstResetEnd < 0).length,
    nonsynchronizingSuffixes: targetExceptions
  },
  sourceProducts,
  counterexamples: {
    ownStartTimesUniversalSubset: collision(
      sourceRecords, "ownSubset", "LE|R|0,0|-1,0|0|106"
    ),
    ownStartTimesExactFinalCarry: collision(
      sourceRecords, "ownFinal", "RO|R|0,0|-2,1|0|45"
    )
  },
  limitations: [
    "Finite replay only; no all-time root invariant or BB(6) proof is claimed.",
    "The own-start phase uses the source drain-summary and correction formulas; their pinned Lean source bridge has not been accepted in this run.",
    "The 211-state subset tracks the image of all 66 possible seeds. It is not the authentic carry when the first-reset output label identifies a particular seed."
  ]
};

const outputDir = path.join(root, "im-results/agent1-623-swindow-obstruction-product");
fs.mkdirSync(outputDir, { recursive: true });
fs.writeFileSync(
  path.join(outputDir, "ConservativeSWindowExactSeedProduct.json"),
  JSON.stringify(result, null, 2) + "\n"
);
console.log(JSON.stringify({
  source: result.sourceWindow,
  target: result.targetWindow,
  products: result.sourceProducts,
  counterexamples: result.counterexamples
}, null, 2));
