#!/usr/bin/env node
"use strict";

// A single reset-carry DFA with two selectable initial states.
// Offset 1 ignores one low output pair; offset 2 ignores two.

const fs = require("node:fs");
const path = require("node:path");

const root = process.cwd();
const here = __dirname;
const bufferPath = path.join(
  root,
  "im-results/agent48-623-tight-window/ResetPostStateDFA_BufferRelative.json"
);
const fullPath = path.join(
  root,
  "im-results/agent49-parity623/ResetPostStateDFA.json"
);
const outputPath = path.join(here, "OffsetSelectedResetDFA.json");

const bufferArtifact = JSON.parse(fs.readFileSync(bufferPath, "utf8"));
const fullArtifact = JSON.parse(fs.readFileSync(fullPath, "utf8"));
const base = bufferArtifact.pair_carry_only;
const full = fullArtifact.post_reset_pair;

const stateMap = base.state_map;
const oldOutputToNew = base.compression.old_output_to_new;
if (stateMap.length !== full.transitions.length) {
  throw new Error("state projection has the wrong source-state count");
}
if (oldOutputToNew.length !== full.output_labels.length) {
  throw new Error("output projection has the wrong source-label count");
}

let transitionProjectionMismatches = 0;
let outputProjectionMismatches = 0;
let eventProjectionMismatches = 0;
const mappedBaseStates = new Set();

for (let source = 0; source < full.transitions.length; source += 1) {
  const baseSource = stateMap[source];
  mappedBaseStates.add(baseSource);

  const fullOutput = full.outputs[source];
  const expectedBaseOutput =
    fullOutput === null ? null : oldOutputToNew[fullOutput];
  if (base.outputs[baseSource] !== expectedBaseOutput) {
    outputProjectionMismatches += 1;
  }

  for (let symbol = 0; symbol < alphabetSize; symbol += 1) {
    const fullTarget = full.transitions[source][symbol];
    const baseTarget = base.transitions[baseSource][symbol];
    if (stateMap[fullTarget] !== baseTarget) {
      transitionProjectionMismatches += 1;
    }

    if (fullOutput === null && full.outputs[fullTarget] !== null) {
      const label = full.output_labels[full.outputs[fullTarget]];
      const eventPair = [
        Math.floor(symbol / 3),
        symbol % 3,
      ];
      if (
        JSON.stringify(label.L_final.previous_pair) !== JSON.stringify(eventPair) ||
        JSON.stringify(label.R_final.previous_pair) !== JSON.stringify(eventPair)
      ) {
        eventProjectionMismatches += 1;
      }
    }
  }
}

const projectionValidation = {
  full_states_checked: full.transitions.length,
  base_states: base.transitions.length,
  mapped_base_states: mappedBaseStates.size,
  full_transitions_checked: full.transitions.length * alphabetSize,
  full_output_labels_checked: full.output_labels.length,
  transition_projection_mismatches: transitionProjectionMismatches,
  output_projection_mismatches: outputProjectionMismatches,
  first_reset_event_symbol_mismatches: eventProjectionMismatches,
};
if (
  mappedBaseStates.size !== base.transitions.length ||
  transitionProjectionMismatches ||
  outputProjectionMismatches ||
  eventProjectionMismatches
) {
  throw new Error("all-state base/full projection check failed: " +
    JSON.stringify(projectionValidation));
}

const alphabetSize = base.transitions[0].length;
if (alphabetSize !== 9) throw new Error("expected nine digit-pair symbols");

const baseCount = base.transitions.length;
const skip1 = baseCount;
const skip2 = baseCount + 1;
const transitions = base.transitions.map((row) => row.slice());
const outputs = base.outputs.concat([null, null]);
const eventMasks = base.transitions.map((row, state) =>
  row.map((target) =>
    base.outputs[state] === null && base.outputs[target] !== null ? 1 : 0
  )
);

// First low pair is ignored by skip1. From skip2, the first pair moves to
// skip1 and the second pair moves to the base initial state.
transitions.push(Array(alphabetSize).fill(base.initial_state));
transitions.push(Array(alphabetSize).fill(skip1));
eventMasks.push(Array(alphabetSize).fill(0));
eventMasks.push(Array(alphabetSize).fill(0));

const states = [];
for (let q = 0; q < baseCount; q += 1) states.push(["base", q]);
states.push(["skip", 1]);
states.push(["skip", 2]);

function assignClasses(keys) {
  const ids = new Map();
  return keys.map((key) => {
    const signature = typeof key === "string" ? key : JSON.stringify(key);
    if (!ids.has(signature)) ids.set(signature, ids.size);
    return ids.get(signature);
  });
}

function samePartition(left, right) {
  const lr = new Map();
  const rl = new Map();
  for (let i = 0; i < left.length; i += 1) {
    if (lr.has(left[i]) && lr.get(left[i]) !== right[i]) return false;
    if (rl.has(right[i]) && rl.get(right[i]) !== left[i]) return false;
    lr.set(left[i], right[i]);
    rl.set(right[i], left[i]);
  }
  return true;
}

let classes = assignClasses(outputs);
const partitionCounts = [new Set(classes).size];
let stable = false;
for (let round = 0; round < 100; round += 1) {
  const signatures = states.map((_, i) => [
    outputs[i],
    transitions[i].map((target, z) => [classes[target], eventMasks[i][z]]),
  ]);
  const nextClasses = assignClasses(signatures);
  partitionCounts.push(new Set(nextClasses).size);
  if (samePartition(classes, nextClasses)) {
    classes = nextClasses;
    stable = true;
    break;
  }
  classes = nextClasses;
}
if (!stable) throw new Error("partition refinement did not stabilize");

const reachable = new Set();
const queue = [skip1, skip2];
reachable.add(skip1);
reachable.add(skip2);
for (let i = 0; i < queue.length; i += 1) {
  for (const target of transitions[queue[i]]) {
    if (!reachable.has(target)) {
      reachable.add(target);
      queue.push(target);
    }
  }
}
if (reachable.size !== states.length) {
  throw new Error("not every state is reachable from the two selected starts");
}

function run(machine, word, initialState) {
  let state = initialState;
  for (const symbol of word) state = machine.transitions[state][symbol];
  return machine.outputs[state];
}

let wordsChecked = 0;
let outputMismatches = 0;
let eventMismatches = 0;
let carryMismatches = 0;

function validateWord(word) {
  for (const offset of [1, 2]) {
    const initialState = offset === 1 ? skip1 : skip2;
    let state = initialState;
    let capturedEvent = null;

    for (const symbol of word) {
      if (eventMasks[state][symbol] !== 0) {
        if (capturedEvent !== null) eventMismatches += 1;
        capturedEvent = symbol;
      }
      state = transitions[state][symbol];
    }

    const fullOutput = run(full, word.slice(offset), full.initial_state);
    if ((capturedEvent === null) !== (fullOutput === null)) {
      outputMismatches += 1;
      continue;
    }
    if (fullOutput === null) continue;

    const fullLabel = full.output_labels[fullOutput];
    const eventPair = [
      Math.floor(capturedEvent / 3),
      capturedEvent % 3,
    ];
    if (
      JSON.stringify(fullLabel.L_final.previous_pair) !== JSON.stringify(eventPair) ||
      JSON.stringify(fullLabel.R_final.previous_pair) !== JSON.stringify(eventPair)
    ) {
      eventMismatches += 1;
    }

    const fullCarryKey =
      fullLabel.L_final.carry.join(",") + "|" +
      fullLabel.R_final.carry.join(",");
    const baseOutput = outputs[state];
    if (
      baseOutput === null ||
      base.output_labels[baseOutput].key !== fullCarryKey
    ) {
      carryMismatches += 1;
    }
  }
  wordsChecked += 1;
}

function enumerateWords(length) {
  function visit(prefix) {
    if (prefix.length === length) {
      validateWord(prefix);
      return;
    }
    for (let symbol = 0; symbol < alphabetSize; symbol += 1) {
      visit(prefix.concat(symbol));
    }
  }
  visit([]);
}

for (let length = 0; length <= 6; length += 1) enumerateWords(length);

if (outputMismatches || eventMismatches || carryMismatches) {
  throw new Error(JSON.stringify({
    outputMismatches,
    eventMismatches,
    carryMismatches,
  }));
}

const result = {
  title: "Offset-selected reset-carry DFA",
  semantics: "choose offset 1 or 2 as the initial state; then read digit pairs",
  alphabet_size: alphabetSize,
  base_state_count: baseCount,
  state_count: states.length,
  initial_state_by_offset: {
    "1": skip1,
    "2": skip2,
  },
  states,
  transitions,
  outputs,
  event_masks: eventMasks,
  projection_validation: projectionValidation,
  minimization: {
    method: "reachable Moore/Mealy partition refinement",
    partition_counts: partitionCounts,
    minimal_state_count: new Set(classes).size,
    transitions_checked: states.length * alphabetSize,
  },
  validation: {
    method: "both selectable starts compared with full post_reset_pair DFA",
    word_lengths: [0, 6],
    words_checked: wordsChecked,
    expected_words: (alphabetSize ** 7 - 1) / (alphabetSize - 1),
    output_mismatches: outputMismatches,
    event_symbol_mismatches: eventMismatches,
    carry_label_mismatches: carryMismatches,
  },
};

fs.writeFileSync(outputPath, JSON.stringify(result, null, 2) + "\n");
console.log(JSON.stringify({
  output_path: path.relative(root, outputPath),
  state_count: result.state_count,
  minimized_state_count: result.minimization.minimal_state_count,
  partition_counts: result.minimization.partition_counts,
  transitions_checked: result.minimization.transitions_checked,
  validation: result.validation,
}, null, 2));
