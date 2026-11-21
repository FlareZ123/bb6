#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");

const root = process.cwd();
const sourcePath = path.join(root, "im-results/agent49-parity623/ResetPostStateDFA.json");
const outputPath = path.join(root, "im-results/agent24-machine623-shifted-reset-product/SourceCarryResetProduct.json");

function mod3(n) {
  return ((n % 3) + 3) % 3;
}
function floor3(n) {
  return Math.floor(n / 3);
}

function buildProduct(branch, full) {
  const baseStateCount = full.transitions.length;
  const skip1 = baseStateCount;
  const skip2 = baseStateCount + 1;
  const dfaStateCount = baseStateCount + 2;
  const cxMin = branch === "L" ? -2 : -4;
  const cxMax = branch === "L" ? 2 : 1;

  const transducerStates = [];
  const transducerIndex = new Map();
  for (let prevX = 0; prevX < 3; prevX++) {
    for (let prevY = 0; prevY < 3; prevY++) {
      for (let carryX = cxMin; carryX <= cxMax; carryX++) {
        for (let carryY = -2; carryY <= 2; carryY++) {
          const key = [prevX, prevY, carryX, carryY].join(",");
          transducerIndex.set(key, transducerStates.length);
          transducerStates.push([prevX, prevY, carryX, carryY]);
        }
      }
    }
  }

  const transducerSteps = transducerStates.map(([prevX, prevY, carryX, carryY]) =>
    Array.from({ length: 9 }, (_, symbol) => {
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
        throw new Error("The claimed carry rectangle is not transition-closed.");
      }
      const nextKey = [x, y, nextCarryX, nextCarryY].join(",");
      const nextTransducerState = transducerIndex.get(nextKey);
      const outputSymbol = 3 * mod3(tx) + mod3(ty);
      return [nextTransducerState, outputSymbol];
    })
  );

  function nextDfaState(state, symbol) {
    if (state < baseStateCount) return full.transitions[state][symbol];
    return state === skip1 ? full.initial_state : skip1;
  }
  function dfaOutput(state) {
    return state < baseStateCount ? full.outputs[state] : null;
  }

  const productStates = [];
  const productIndex = new Map();
  const productTransitions = [];
  function addState(transducerState, dfaState) {
    const key = transducerState * dfaStateCount + dfaState;
    let index = productIndex.get(key);
    if (index === undefined) {
      index = productStates.length;
      productIndex.set(key, index);
      productStates.push([transducerState, dfaState]);
    }
    return index;
  }

  const startIds = { "1": [], "2": [] };
  for (let t = 0; t < transducerStates.length; t++) {
    startIds["1"].push(addState(t, skip1));
    startIds["2"].push(addState(t, skip2));
  }

  for (let i = 0; i < productStates.length; i++) {
    const [transducerState, dfaState] = productStates[i];
    productTransitions[i] = transducerSteps[transducerState].map(
      ([nextTransducerState, outputSymbol]) =>
        addState(nextTransducerState, nextDfaState(dfaState, outputSymbol))
    );
  }

  const productOutputs = productStates.map(([, dfaState]) => dfaOutput(dfaState));
  let classes = productOutputs.map(output => output === null ? 54 : output);
  const partitionCounts = [new Set(classes).size];
  let stable = false;

  for (let round = 0; round < 40; round++) {
    const signatureIndex = new Map();
    const nextClasses = [];
    for (let i = 0; i < productStates.length; i++) {
      const signature = [
        productOutputs[i] === null ? -1 : productOutputs[i],
        ...productTransitions[i].map(next => classes[next])
      ].join(",");
      let classId = signatureIndex.get(signature);
      if (classId === undefined) {
        classId = signatureIndex.size;
        signatureIndex.set(signature, classId);
      }
      nextClasses[i] = classId;
    }

    partitionCounts.push(signatureIndex.size);
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
  if (!stable) throw new Error("Moore partition refinement did not stabilize.");

  const minimizedStateCount = new Set(classes).size;
  const representatives = Array(minimizedStateCount).fill(-1);
  for (let i = 0; i < classes.length; i++) {
    if (representatives[classes[i]] === -1) representatives[classes[i]] = i;
  }
  const quotientOutputs = representatives.map(i => productOutputs[i]);
  const quotientTransitions = representatives.map(i =>
    productTransitions[i].map(next => classes[next])
  );

  for (let i = 0; i < productStates.length; i++) {
    const classId = classes[i];
    if (productOutputs[i] !== quotientOutputs[classId]) {
      throw new Error("Quotient output certificate failed.");
    }
    for (let symbol = 0; symbol < 9; symbol++) {
      if (classes[productTransitions[i][symbol]] !== quotientTransitions[classId][symbol]) {
        throw new Error("Quotient transition certificate failed.");
      }
    }
  }

  return {
    branch,
    carry_bounds: {
      prev_x: [0, 2],
      prev_y: [0, 2],
      carry_x: [cxMin, cxMax],
      carry_y: [-2, 2]
    },
    transducer_states: transducerStates,
    product_states: productStates,
    class_of_product_state: classes,
    initial_classes_by_offset: {
      "1": startIds["1"].map(i => classes[i]),
      "2": startIds["2"].map(i => classes[i])
    },
    quotient_outputs: quotientOutputs,
    quotient_transitions: quotientTransitions,
    partition_counts: partitionCounts,
    product_state_count: productStates.length,
    minimized_state_count: minimizedStateCount,
    product_transition_count: productTransitions.length * 9
  };
}

const source = JSON.parse(fs.readFileSync(sourcePath, "utf8"));
const full = source.post_reset_pair;
const artifact = {
  schema: "bb6-machine623-source-carry-reset-product-v1",
  description: "Reachable product of the branch-specific source-to-target carry transducer and the full post_reset_pair DFA, with one- and two-symbol output skips.",
  source_dfa: "im-results/agent49-parity623/ResetPostStateDFA.json",
  full_dfa_state_count: full.transitions.length,
  full_dfa_output_labels: full.output_labels,
  skip_state_ids: {
    offset1: full.transitions.length,
    offset2: full.transitions.length + 1
  },
  alphabet: "pair digit symbols 3*x_digit + y_digit, ordered lexicographically with x_digit,y_digit in {0,1,2}",
  products: {
    L: buildProduct("L", full),
    R: buildProduct("R", full)
  }
};

const serialized = JSON.stringify(artifact, null, 2) + "\n";
if (process.argv.includes("--verify")) {
  const existing = JSON.parse(fs.readFileSync(outputPath, "utf8"));
  if (JSON.stringify(existing) !== JSON.stringify(artifact)) {
    throw new Error("Stored product artifact differs from regenerated artifact.");
  }
  process.stdout.write("Verified SourceCarryResetProduct.json\n");
} else {
  fs.writeFileSync(outputPath, serialized);
  process.stdout.write("Wrote SourceCarryResetProduct.json (" + serialized.length + " bytes)\n");
}
