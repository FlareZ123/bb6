#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");

const root = process.cwd();
const artifactPath = path.join(root, "im-results/agent24-machine623-shifted-reset-product/SourceDerivedResetProduct.json");
const oldDfaPath = path.join(root, "im-results/agent32-623-phase-automaton/ResetPatternDFA.json");
const artifact = JSON.parse(fs.readFileSync(artifactPath, "utf8"));
const oldDfa = JSON.parse(fs.readFileSync(oldDfaPath, "utf8"));
const resetDfa = artifact.reset_pattern_dfa;
const acceptingDfa = new Set(resetDfa.accepting_states);
const dfaCount = resetDfa.state_count;
const skip1 = dfaCount;
const skip2 = dfaCount + 1;
const productDfaCount = dfaCount + 2;

function mod3(n) {
  return ((n % 3) + 3) % 3;
}
function floor3(n) {
  return Math.floor(n / 3);
}
function makeTransducer(branch) {
  const minX = branch === "L" ? -2 : -4;
  const maxX = branch === "L" ? 2 : 1;
  const states = [];
  const index = new Map();
  for (let prevX = 0; prevX < 3; prevX++) {
    for (let prevY = 0; prevY < 3; prevY++) {
      for (let carryX = minX; carryX <= maxX; carryX++) {
        for (let carryY = -2; carryY <= 2; carryY++) {
          index.set([prevX, prevY, carryX, carryY].join(","), states.length);
          states.push([prevX, prevY, carryX, carryY]);
        }
      }
    }
  }
  const next = new Int32Array(states.length * 9);
  const xFlags = new Uint8Array(states.length * 9);
  for (let state = 0; state < states.length; state++) {
    const [prevX, prevY, carryX, carryY] = states[state];
    for (let x = 0; x < 3; x++) {
      for (let y = 0; y < 3; y++) {
        const tx = branch === "L"
          ? x - prevY + carryX
          : -x - prevX - prevY + carryX;
        const ty = branch === "L"
          ? prevY + carryY
          : prevX + prevY + carryY;
        const nextCarryX = floor3(tx);
        const nextCarryY = floor3(ty);
        if (
          nextCarryX < minX || nextCarryX > maxX ||
          nextCarryY < -2 || nextCarryY > 2
        ) throw new Error(branch + ": full carry rectangle is not closed");
        const j = state * 9 + x * 3 + y;
        next[j] = index.get([x, y, nextCarryX, nextCarryY].join(","));
        const outX = mod3(tx);
        xFlags[j] = (outX !== 0 ? 1 : 0) | (outX !== 2 ? 2 : 0);
      }
    }
  }
  return { branch, minX, maxX, states, index, next, xFlags };
}

function sourceStarts(transducer) {
  const starts = [];
  for (let prevX = 0; prevX < 3; prevX++) {
    for (let prevY = 0; prevY < 3; prevY++) {
      const minX = transducer.branch === "L" ? -2 : -4;
      const maxX = transducer.branch === "L" ? 1 : 0;
      const minY = -1;
      const maxY = transducer.branch === "L" ? 1 : 2;
      for (let carryX = minX; carryX <= maxX; carryX++) {
        for (let carryY = minY; carryY <= maxY; carryY++) {
          starts.push(transducer.index.get(
            [prevX, prevY, carryX, carryY].join(",")
          ));
        }
      }
    }
  }
  return starts;
}

function verifyDirectReset(transducer, starts, branch) {
  const word = artifact.direct_three_symbol_reset.word;
  let commonFinal = null;
  for (const start of starts) {
    let state = start;
    let flags = 0;
    for (const symbol of word) {
      const j = state * 9 + symbol;
      flags |= transducer.xFlags[j];
      state = transducer.next[j];
    }
    if (flags !== 3) throw new Error(branch + ": three-symbol word is monochromatic");
    if (commonFinal === null) commonFinal = state;
    else if (state !== commonFinal) throw new Error(branch + ": three-symbol word does not synchronize");
  }
  const finalState = transducer.states[commonFinal];
  if (JSON.stringify(finalState) !== JSON.stringify([0, 0, -1, 0])) {
    throw new Error(branch + ": unexpected three-symbol reset state");
  }
  return finalState;
}

function verifyLanguageInclusion() {
  const oldAccepting = new Set(oldDfa.accepting_states);
  const newAccepting = acceptingDfa;
  const seen = new Set();
  const queue = [[oldDfa.initial_state, resetDfa.initial_state, []]];
  let oldOnly = null;
  let newOnly = null;
  for (let head = 0; head < queue.length; head++) {
    const [oldState, newState, word] = queue[head];
    const key = oldState + "," + newState;
    if (seen.has(key)) continue;
    seen.add(key);
    if (oldAccepting.has(oldState) && !newAccepting.has(newState) && oldOnly === null) oldOnly = word;
    if (newAccepting.has(newState) && !oldAccepting.has(oldState) && newOnly === null) newOnly = word;
    if (oldOnly !== null && newOnly !== null) break;
    for (let symbol = 0; symbol < 9; symbol++) {
      queue.push([
        oldDfa.transitions[oldState][symbol],
        resetDfa.transitions[newState][symbol],
        word.length < 10 ? word.concat(symbol) : word
      ]);
    }
  }
  const expected = artifact.language_comparison_with_full_rectangle_dfa;
  if (oldOnly !== null) throw new Error("Full-rectangle language is not included in source-derived language");
  if (JSON.stringify(newOnly) !== JSON.stringify(expected.shortest_source_only_witness)) {
    throw new Error("Source-only witness mismatch");
  }
  if (seen.size !== expected.product_pairs_visited) throw new Error("Language-inclusion product size mismatch");
  return { oldSubsetNew: true, newOnlyWitness: newOnly, pairsVisited: seen.size };
}

function verifyProduct(branch, transducer, starts) {
  const product = artifact.products[branch];
  if (JSON.stringify(product.transducer_states) !== JSON.stringify(transducer.states)) {
    throw new Error(branch + ": transducer state table mismatch");
  }
  if (JSON.stringify(product.source_start_transducer_ids) !== JSON.stringify(starts)) {
    throw new Error(branch + ": source-derived start set mismatch");
  }

  const productIndex = new Map();
  for (let i = 0; i < product.product_states.length; i++) {
    const [t, d] = product.product_states[i];
    productIndex.set(t * productDfaCount + d, i);
  }

  const rows = Array(product.product_states.length);
  const outputs = Array(product.product_states.length);
  let transitionCount = 0;
  for (let i = 0; i < product.product_states.length; i++) {
    const [t, d] = product.product_states[i];
    outputs[i] = d < dfaCount && acceptingDfa.has(d) ? 1 : 0;
    const classId = product.class_of_product_state[i];
    if (outputs[i] !== product.quotient_outputs[classId]) {
      throw new Error(branch + ": quotient output mismatch");
    }

    rows[i] = Array(9);
    const [prevX, prevY, carryX, carryY] = transducer.states[t];
    for (let symbol = 0; symbol < 9; symbol++) {
      const x = Math.floor(symbol / 3);
      const y = symbol % 3;
      const tx = branch === "L"
        ? x - prevY + carryX
        : -x - prevX - prevY + carryX;
      const ty = branch === "L"
        ? prevY + carryY
        : prevX + prevY + carryY;
      const nextT = transducer.next[t * 9 + symbol];
      const outputSymbol = 3 * mod3(tx) + mod3(ty);
      const nextD = d < dfaCount
        ? resetDfa.transitions[d][outputSymbol]
        : (d === skip1 ? resetDfa.initial_state : skip1);
      const nextProduct = productIndex.get(nextT * productDfaCount + nextD);
      if (nextProduct === undefined) throw new Error(branch + ": missing product transition");
      rows[i][symbol] = nextProduct;
      transitionCount++;
      if (
        product.class_of_product_state[nextProduct] !==
        product.quotient_transitions[classId][symbol]
      ) throw new Error(branch + ": quotient transition mismatch");
    }
  }

  const startIds = { "1": [], "2": [] };
  for (const offset of ["1", "2"]) {
    const d = offset === "1" ? skip1 : skip2;
    for (let i = 0; i < starts.length; i++) {
      const state = productIndex.get(starts[i] * productDfaCount + d);
      if (state === undefined) throw new Error(branch + ": missing offset start");
      startIds[offset].push(state);
      if (product.class_of_product_state[state] !== product.initial_classes_by_offset[offset][i]) {
        throw new Error(branch + ": initial quotient class mismatch");
      }
    }
  }

  const seen = new Uint8Array(product.product_states.length);
  const queue = [];
  for (const offset of ["1", "2"]) {
    for (const state of startIds[offset]) {
      if (!seen[state]) {
        seen[state] = 1;
        queue.push(state);
      }
    }
  }
  for (let head = 0; head < queue.length; head++) {
    for (const next of rows[queue[head]]) {
      if (!seen[next]) {
        seen[next] = 1;
        queue.push(next);
      }
    }
  }
  if (queue.length !== product.product_states.length) {
    throw new Error(branch + ": product contains unreachable states");
  }

  const acceptingIds = [];
  for (let i = 0; i < outputs.length; i++) if (outputs[i] === 1) acceptingIds.push(i);
  const acceptedClosed = acceptingIds.every(i => rows[i].every(j => outputs[j] === 1));
  if (!acceptedClosed || !product.accepted_region_closed) {
    throw new Error(branch + ": accepting product region is not closed");
  }
  if (acceptingIds.length !== product.accepting_product_state_count) {
    throw new Error(branch + ": accepting product state count mismatch");
  }

  const acceptingTransducerStates = [...new Set(
    acceptingIds.map(i => product.product_states[i][0])
  )].sort((a, b) => a - b).map(i => transducer.states[i]);
  if (JSON.stringify(acceptingTransducerStates) !== JSON.stringify(product.accepting_transducer_states)) {
    throw new Error(branch + ": accepting transducer state set mismatch");
  }

  let classes = Uint32Array.from(outputs);
  const partitionCounts = [new Set(classes).size];
  let stable = false;
  for (let round = 0; round < 40; round++) {
    const signatures = new Map();
    const nextClasses = new Uint32Array(product.product_states.length);
    for (let i = 0; i < product.product_states.length; i++) {
      const signature = outputs[i] + "," + rows[i].map(j => classes[j]).join(",");
      let id = signatures.get(signature);
      if (id === undefined) {
        id = signatures.size;
        signatures.set(signature, id);
      }
      nextClasses[i] = id;
    }
    partitionCounts.push(signatures.size);
    const oldToNew = new Map();
    const newToOld = new Map();
    stable = true;
    for (let i = 0; i < classes.length; i++) {
      if (oldToNew.has(classes[i]) && oldToNew.get(classes[i]) !== nextClasses[i]) stable = false;
      if (newToOld.has(nextClasses[i]) && newToOld.get(nextClasses[i]) !== classes[i]) stable = false;
      oldToNew.set(classes[i], nextClasses[i]);
      newToOld.set(nextClasses[i], classes[i]);
    }
    classes = nextClasses;
    if (stable) break;
  }
  if (!stable) throw new Error(branch + ": Moore refinement did not stabilize");
  if (new Set(classes).size !== product.minimized_state_count) {
    throw new Error(branch + ": minimized state count mismatch");
  }
  if (JSON.stringify(partitionCounts) !== JSON.stringify(product.partition_counts)) {
    throw new Error(branch + ": partition sequence mismatch");
  }

  const storedToComputed = new Map();
  const computedToStored = new Map();
  for (let i = 0; i < classes.length; i++) {
    const stored = product.class_of_product_state[i];
    const computed = classes[i];
    if (storedToComputed.has(stored) && storedToComputed.get(stored) !== computed) {
      throw new Error(branch + ": stored class map is not the stable partition");
    }
    if (computedToStored.has(computed) && computedToStored.get(computed) !== stored) {
      throw new Error(branch + ": stored class map merges distinct states");
    }
    storedToComputed.set(stored, computed);
    computedToStored.set(computed, stored);
  }

  return {
    branch,
    productStates: product.product_states.length,
    transitions: transitionCount,
    minimizedStates: product.minimized_state_count,
    acceptingProductStates: acceptingIds.length,
    reachableStates: queue.length,
    partitionCounts
  };
}

const L = makeTransducer("L");
const R = makeTransducer("R");
const startsL = sourceStarts(L);
const startsR = sourceStarts(R);
if (startsL.length !== 108 || startsR.length !== 180) {
  throw new Error("Source-derived start-set sizes mismatch");
}
const finalL = verifyDirectReset(L, startsL, "L");
const finalR = verifyDirectReset(R, startsR, "R");
if (
  JSON.stringify(finalL) !== JSON.stringify(artifact.direct_three_symbol_reset.L.finalState) ||
  JSON.stringify(finalR) !== JSON.stringify(artifact.direct_three_symbol_reset.R.finalState)
) throw new Error("Direct reset-word certificate mismatch");

const excluded = L.index.get([0, 0, 2, -2].join(","));
let excludedFlags = 0;
let excludedState = excluded;
for (const symbol of [1, 0, 0]) {
  const j = excludedState * 9 + symbol;
  excludedFlags |= L.xFlags[j];
  excludedState = L.next[j];
}
if (excludedFlags === 3) throw new Error("Full-L counterexample no longer fails nonmonochromaticity");

const language = verifyLanguageInclusion();
const summary = {
  sourceStarts: { L: startsL.length, R: startsR.length },
  resetDfaStates: resetDfa.state_count,
  resetDfaAccepting: resetDfa.accepting_states,
  oldLanguageIncluded: language.oldSubsetNew,
  newOnlyWitness: language.newOnlyWitness,
  directResetFinalState: [0, 0, -1, 0],
  L: verifyProduct("L", L, startsL),
  R: verifyProduct("R", R, startsR)
};
process.stdout.write(JSON.stringify(summary, null, 2) + "\n");
