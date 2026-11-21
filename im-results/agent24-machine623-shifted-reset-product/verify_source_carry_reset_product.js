#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");

const root = process.cwd();
const sourcePath = path.join(root, "im-results/agent49-parity623/ResetPostStateDFA.json");
const productPath = path.join(root, "im-results/agent24-machine623-shifted-reset-product/SourceCarryResetProduct.json");
const source = JSON.parse(fs.readFileSync(sourcePath, "utf8"));
const artifact = JSON.parse(fs.readFileSync(productPath, "utf8"));
const full = source.post_reset_pair;
const baseCount = full.transitions.length;
const skip1 = baseCount;
const skip2 = baseCount + 1;
const dfaCount = baseCount + 2;

function mod3(n) {
  return ((n % 3) + 3) % 3;
}
function floor3(n) {
  return Math.floor(n / 3);
}
function nextDfaState(state, symbol) {
  if (state < baseCount) return full.transitions[state][symbol];
  return state === skip1 ? full.initial_state : skip1;
}
function outputOfDfaState(state) {
  return state < baseCount ? full.outputs[state] : null;
}

function verifyBranch(branch) {
  const product = artifact.products[branch];
  const cxMin = branch === "L" ? -2 : -4;
  const cxMax = branch === "L" ? 2 : 1;
  const expectedTransducerStates = [];
  const transducerIndex = new Map();

  for (let prevX = 0; prevX < 3; prevX++) {
    for (let prevY = 0; prevY < 3; prevY++) {
      for (let carryX = cxMin; carryX <= cxMax; carryX++) {
        for (let carryY = -2; carryY <= 2; carryY++) {
          const key = [prevX, prevY, carryX, carryY].join(",");
          transducerIndex.set(key, expectedTransducerStates.length);
          expectedTransducerStates.push([prevX, prevY, carryX, carryY]);
        }
      }
    }
  }

  if (JSON.stringify(product.transducer_states) !== JSON.stringify(expectedTransducerStates)) {
    throw new Error(branch + ": transducer-state enumeration mismatch");
  }
  if (product.product_states.length !== product.product_state_count) {
    throw new Error(branch + ": product-state count mismatch");
  }
  if (product.class_of_product_state.length !== product.product_state_count) {
    throw new Error(branch + ": class-map length mismatch");
  }

  const productIndex = new Map();
  for (let i = 0; i < product.product_states.length; i++) {
    const [transducerState, dfaState] = product.product_states[i];
    productIndex.set(transducerState * dfaCount + dfaState, i);
  }

  const rows = Array(product.product_states.length);
  const outputs = Array(product.product_states.length);
  const startIds = { "1": [], "2": [] };
  let transitionCount = 0;

  for (let i = 0; i < product.product_states.length; i++) {
    const [transducerState, dfaState] = product.product_states[i];
    const [prevX, prevY, carryX, carryY] = expectedTransducerStates[transducerState];
    outputs[i] = outputOfDfaState(dfaState);

    if (outputs[i] !== product.quotient_outputs[product.class_of_product_state[i]]) {
      throw new Error(branch + ": quotient output mismatch at product state " + i);
    }

    rows[i] = Array(9);
    for (let symbol = 0; symbol < 9; symbol++) {
      const x = Math.floor(symbol / 3);
      const y = symbol % 3;
      const tx = branch === "L"
        ? x - prevY + carryX
        : -x - prevX - prevY + carryX;
      const ty = branch === "L"
        ? prevY + carryY
        : prevX + prevY + carryY;
      const nextCarryX = floor3(tx);
      const nextCarryY = floor3(ty);

      if (
        nextCarryX < cxMin || nextCarryX > cxMax ||
        nextCarryY < -2 || nextCarryY > 2
      ) {
        throw new Error(branch + ": carry rectangle not closed");
      }

      const nextTransducerState = transducerIndex.get(
        [x, y, nextCarryX, nextCarryY].join(",")
      );
      const outputSymbol = 3 * mod3(tx) + mod3(ty);
      const nextDfa = nextDfaState(dfaState, outputSymbol);
      const nextProduct = productIndex.get(nextTransducerState * dfaCount + nextDfa);
      if (nextProduct === undefined) {
        throw new Error(branch + ": missing product transition");
      }

      rows[i][symbol] = nextProduct;
      transitionCount++;
      const quotientClass = product.class_of_product_state[i];
      if (
        product.class_of_product_state[nextProduct] !==
        product.quotient_transitions[quotientClass][symbol]
      ) {
        throw new Error(branch + ": quotient transition mismatch");
      }
    }
  }

  for (const offset of ["1", "2"]) {
    const skipState = offset === "1" ? skip1 : skip2;
    for (let t = 0; t < expectedTransducerStates.length; t++) {
      const productState = productIndex.get(t * dfaCount + skipState);
      if (productState === undefined) {
        throw new Error(branch + ": missing offset-" + offset + " start state");
      }
      startIds[offset].push(productState);
      if (
        product.class_of_product_state[productState] !==
        product.initial_classes_by_offset[offset][t]
      ) {
        throw new Error(branch + ": offset-" + offset + " initial class mismatch");
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
    throw new Error(branch + ": stored product contains unreachable states");
  }

  let classes = outputs.map(output => output === null ? 54 : output);
  const partitionCounts = [new Set(classes).size];
  let stable = false;

  for (let round = 0; round < 40; round++) {
    const signatures = new Map();
    const nextClasses = [];
    for (let i = 0; i < product.product_states.length; i++) {
      const signature = [
        outputs[i] === null ? -1 : outputs[i],
        ...rows[i].map(next => classes[next])
      ].join(",");
      let classId = signatures.get(signature);
      if (classId === undefined) {
        classId = signatures.size;
        signatures.set(signature, classId);
      }
      nextClasses[i] = classId;
    }
    partitionCounts.push(signatures.size);

    const oldToNew = new Map();
    const newToOld = new Map();
    stable = true;
    for (let i = 0; i < classes.length; i++) {
      if (oldToNew.has(classes[i]) && oldToNew.get(classes[i]) !== nextClasses[i]) {
        stable = false;
      }
      if (newToOld.has(nextClasses[i]) && newToOld.get(nextClasses[i]) !== classes[i]) {
        stable = false;
      }
      oldToNew.set(classes[i], nextClasses[i]);
      newToOld.set(nextClasses[i], classes[i]);
    }
    classes = nextClasses;
    if (stable) break;
  }

  if (!stable) throw new Error(branch + ": minimization did not stabilize");
  if (new Set(classes).size !== product.minimized_state_count) {
    throw new Error(branch + ": minimized state count mismatch");
  }
  if (JSON.stringify(partitionCounts) !== JSON.stringify(product.partition_counts)) {
    throw new Error(branch + ": partition-refinement sequence mismatch");
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
      throw new Error(branch + ": stored class map merges distinguishable classes");
    }
    storedToComputed.set(stored, computed);
    computedToStored.set(computed, stored);
  }

  return {
    branch,
    productStates: product.product_states.length,
    productTransitions: transitionCount,
    minimizedStates: product.minimized_state_count,
    reachableStates: queue.length,
    partitionCounts
  };
}

if (JSON.stringify(artifact.full_dfa_output_labels) !== JSON.stringify(full.output_labels)) {
  throw new Error("The product artifact was built from a different full-DFA output table.");
}
const summary = {
  L: verifyBranch("L"),
  R: verifyBranch("R")
};
process.stdout.write(JSON.stringify(summary, null, 2) + "\n");
