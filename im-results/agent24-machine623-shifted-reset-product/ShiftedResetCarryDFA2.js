#!/usr/bin/env node
"use strict";

// Two-copy shifted reset-carry product. The target S-window always begins
// after one or two low output pairs, so offset 0 is never selected.

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
const outputPath = path.join(here, "ShiftedResetCarryDFA2.json");

const bufferArtifact = JSON.parse(fs.readFileSync(bufferPath, "utf8"));
const fullArtifact = JSON.parse(fs.readFileSync(fullPath, "utf8"));
const base = bufferArtifact.pair_carry_only;
const full = fullArtifact.post_reset_pair;

const alphabetSize = base.transitions[0].length;
if (alphabetSize !== 9) throw new Error("expected nine digit-pair symbols");

const baseInitial = base.initial_state;
const states = [];
const stateIds = new Map();
const transitions = [];
const eventMasks = [];

function addState(state) {
  const key = state.join(",");
  if (!stateIds.has(key)) {
    stateIds.set(key, states.length);
    states.push(state);
  }
  return stateIds.get(key);
}

// State [t,c1,c2], where t=min(2, consumed symbols). Copy 1 skips the
// first symbol; copy 2 skips the first two symbols.
const initialState = addState([0, baseInitial, baseInitial]);

for (let i = 0; i < states.length; i += 1) {
  const [t, oldCopy1, oldCopy2] = states[i];
  const oldCopies = [oldCopy1, oldCopy2];
  const nextRow = [];
  const eventRow = [];

  for (let z = 0; z < alphabetSize; z += 1) {
    const nextCopies = [];
    let eventMask = 0;

    for (let j = 0; j < 2; j += 1) {
      const offset = j + 1;
      const oldState = oldCopies[j];
      const nextState = t >= offset
        ? base.transitions[oldState][z]
        : baseInitial;
      nextCopies.push(nextState);

      const oldOutput = base.outputs[oldState];
      const nextOutput = base.outputs[nextState];
      if (t >= offset && oldOutput === null && nextOutput !== null) {
        eventMask |= 1 << j;
      }
    }

    nextRow.push(addState([Math.min(2, t + 1), ...nextCopies]));
    eventRow.push(eventMask);
  }

  transitions[i] = nextRow;
  eventMasks[i] = eventRow;
}

const outputs = states.map(([t, copy1, copy2]) => [
  t >= 1 ? (base.outputs[copy1] ?? null) : null,
  t >= 2 ? (base.outputs[copy2] ?? null) : null,
]);

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

// Moore outputs are the two suffix carry labels; Mealy outputs are the
// event bits recording the final symbol of each first reset witness.
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
const minimizedStateCount = new Set(classes).size;

function run(machine, word) {
  let state = machine.initial_state;
  for (const symbol of word) state = machine.transitions[state][symbol];
  return machine.outputs[state];
}

let wordsChecked = 0;
let outputMismatches = 0;
let eventMismatches = 0;
let carryMismatches = 0;
let fullLabelLookupMismatches = 0;

function validateWord(word) {
  let productState = initialState;
  const capturedEvents = [null, null];

  for (const symbol of word) {
    const mask = eventMasks[productState][symbol];
    for (let j = 0; j < 2; j += 1) {
      if (mask & (1 << j)) {
        if (capturedEvents[j] !== null) eventMismatches += 1;
        capturedEvents[j] = symbol;
      }
    }
    productState = transitions[productState][symbol];
  }

  const finalState = states[productState];
  for (let j = 0; j < 2; j += 1) {
    const offset = j + 1;
    const fullOutput = run(full, word.slice(offset));
    if ((capturedEvents[j] === null) !== (fullOutput === null)) {
      outputMismatches += 1;
      continue;
    }
    if (fullOutput === null) continue;

    const fullLabel = full.output_labels[fullOutput];
    const eventPair = [
      Math.floor(capturedEvents[j] / 3),
      capturedEvents[j] % 3,
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
    const baseOutput = base.outputs[finalState[offset]];
    if (fullOutputLookup[capturedEvents[j]][baseOutput] !== fullOutput) {
      fullLabelLookupMismatches += 1;
    }
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

for (let length = 0; length <= 6; length += 1) {
  enumerateWords(length);
}

if (outputMismatches || eventMismatches || carryMismatches || fullLabelLookupMismatches) {
  throw new Error(JSON.stringify({
    outputMismatches,
    eventMismatches,
    carryMismatches,
    fullLabelLookupMismatches,
  }));
}

const eventTransitionCounts = [0, 0];
const eventMaskHistogram = {};
for (const row of eventMasks) {
  for (const mask of row) {
    eventMaskHistogram[mask] = (eventMaskHistogram[mask] || 0) + 1;
    for (let j = 0; j < 2; j += 1) {
      if (mask & (1 << j)) eventTransitionCounts[j] += 1;
    }
  }
}

const result = {
  title: "Two-copy shifted reset-carry product",
  semantics: "copy 1 skips one symbol; copy 2 skips two symbols",
  alphabet_size: alphabetSize,
  base_state_count: base.transitions.length,
  base_output_label_count: base.output_labels.length,
  state_count: states.length,
  initial_state: initialState,
  states,
  transitions,
  outputs,
  event_masks: eventMasks,
  full_output_lookup: fullOutputLookup,
  full_output_labels: full.output_labels,
  projection_validation: projectionValidation,
  minimization: {
    method: "reachable Moore/Mealy partition refinement",
    partition_counts: partitionCounts,
    minimal_state_count: minimizedStateCount,
    transitions_checked: states.length * alphabetSize,
  },
  validation: {
    method: "exhaustive comparison with full post_reset_pair DFA",
    word_lengths: [0, 6],
    words_checked: wordsChecked,
    expected_words: (alphabetSize ** 7 - 1) / (alphabetSize - 1),
    output_mismatches: outputMismatches,
    event_symbol_mismatches: eventMismatches,
    carry_label_mismatches: carryMismatches,
    full_label_lookup_mismatches: fullLabelLookupMismatches,
    offset_cases_checked: wordsChecked * 2,
    event_transition_counts_by_offset: eventTransitionCounts,
    event_mask_histogram: eventMaskHistogram,
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
