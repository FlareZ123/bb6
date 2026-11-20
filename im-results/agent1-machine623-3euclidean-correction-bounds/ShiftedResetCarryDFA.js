#!/usr/bin/env node
"use strict";

/*
 * Three-offset first-common-reset carry interface for the #623 moving window.
 *
 * Build three copies of the buffer-relative 349-state pair-carry output DFA.
 * Copy k reads the input word after dropping its first k symbols, k=0,1,2.
 * The product records all three carry-profile outputs and a Mealy event mask.
 *
 * If bit k of event_masks[state][z] is set, symbol z is the final symbol of
 * the first reset witness in suffix k. It therefore recovers previous_pair
 * as [Math.floor(z/3), z%3], exactly as required by the buffer-relative DFA.
 *
 * Reproduction:
 *   node im-results/agent1-machine623-3euclidean-correction-bounds/ShiftedResetCarryDFA.js
 *
 * Output:
 *   im-results/agent1-machine623-3euclidean-correction-bounds/ShiftedResetCarryDFA.json
 *
 * The product is exact as an automaton composition. It does NOT establish
 * that authentic #623 root windows enter or preserve the reset language.
 */

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
const outputPath = path.join(here, "ShiftedResetCarryDFA.json");

const bufferArtifact = JSON.parse(fs.readFileSync(bufferPath, "utf8"));
const fullArtifact = JSON.parse(fs.readFileSync(fullPath, "utf8"));
const base = bufferArtifact.pair_carry_only;
const full = fullArtifact.post_reset_pair;

const alphabetSize = base.transitions[0].length;
if (alphabetSize !== 9) throw new Error("expected the nine digit-pair symbols");

const maxShift = 2;
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

const initialState = addState([
  0,
  baseInitial,
  baseInitial,
  baseInitial,
]);

/*
 * t=min(2, symbols consumed). Copy k skips the first k symbols, then reads
 * every subsequent symbol. At t=k, the next symbol starts copy k.
 */
for (let i = 0; i < states.length; i += 1) {
  const [t, ...oldCopies] = states[i];
  const nextRow = [];
  const eventRow = [];

  for (let z = 0; z < alphabetSize; z += 1) {
    const nextCopies = [];
    let eventMask = 0;

    for (let k = 0; k <= maxShift; k += 1) {
      const oldState = oldCopies[k];
      const nextState = t >= k
        ? base.transitions[oldState][z]
        : baseInitial;
      nextCopies.push(nextState);

      const oldOutput = base.outputs[oldState];
      const nextOutput = base.outputs[nextState];
      if (t >= k && oldOutput === null && nextOutput !== null) {
        eventMask |= 1 << k;
      }
    }

    nextRow.push(addState([Math.min(maxShift, t + 1), ...nextCopies]));
    eventRow.push(eventMask);
  }

  transitions[i] = nextRow;
  eventMasks[i] = eventRow;
}

const outputs = states.map(([t, ...copies]) =>
  copies.map((state, k) => t >= k ? (base.outputs[state] ?? null) : null)
);

/*
 * Minimize as a deterministic Moore/Mealy machine. The Moore output is the
 * triple of carry-profile labels; the Mealy output is the event bitmask for
 * each input symbol. The event is determined by the old/new output labels,
 * but it is included explicitly in the refinement signature.
 */
let classes = [];
const initialClasses = new Map();
for (let i = 0; i < states.length; i += 1) {
  const key = JSON.stringify(outputs[i]);
  if (!initialClasses.has(key)) initialClasses.set(key, initialClasses.size);
  classes[i] = initialClasses.get(key);
}

const partitionCounts = [new Set(classes).size];
for (let iteration = 0; iteration < 100; iteration += 1) {
  const signatures = new Map();
  const nextClasses = new Array(states.length);

  for (let i = 0; i < states.length; i += 1) {
    const signature = JSON.stringify([
      outputs[i],
      transitions[i].map((target, z) => [classes[target], eventMasks[i][z]]),
    ]);
    if (!signatures.has(signature)) signatures.set(signature, signatures.size);
    nextClasses[i] = signatures.get(signature);
  }

  partitionCounts.push(new Set(nextClasses).size);
  const stable = nextClasses.every((value, index) => value === classes[index]);
  classes = nextClasses;
  if (stable) break;
}

const minimizedStateCount = new Set(classes).size;
if (minimizedStateCount !== states.length) {
  throw new Error(
    "reachable product did not remain minimal: " +
    minimizedStateCount + " < " + states.length
  );
}

/*
 * Exhaustively compare all 597,871 words of lengths 0..6. Every reset witness
 * has length at most six, so this checks all possible first-witness outputs
 * and all event-symbol/previous_pair recoveries at the shortest complete
 * witness horizon.
 */
function run(machine, word) {
  let state = machine.initial_state;
  for (const symbol of word) state = machine.transitions[state][symbol];
  const output = machine.outputs[state];
  return output === null ? null : output;
}

let wordsChecked = 0;
let outputMismatches = 0;
let eventMismatches = 0;
let carryMismatches = 0;

for (let length = 0; length <= 6; length += 1) {
  const wordCount = alphabetSize ** length;

  for (let code = 0; code < wordCount; code += 1) {
    let quotient = code;
    const word = new Array(length);

    for (let i = length - 1; i >= 0; i -= 1) {
      word[i] = quotient % alphabetSize;
      quotient = Math.floor(quotient / alphabetSize);
    }

    let productState = initialState;
    const capturedEvents = [null, null, null];

    for (const symbol of word) {
      const mask = eventMasks[productState][symbol];
      for (let k = 0; k <= maxShift; k += 1) {
        if (mask & (1 << k)) {
          if (capturedEvents[k] !== null) eventMismatches += 1;
          capturedEvents[k] = symbol;
        }
      }
      productState = transitions[productState][symbol];
    }

    for (let k = 0; k <= maxShift; k += 1) {
      const suffix = word.slice(k);
      const expected = run(base, suffix);
      if (outputs[productState][k] !== expected) outputMismatches += 1;

      const fullOutput = run(full, suffix);
      if (expected === null) {
        if (capturedEvents[k] !== null || fullOutput !== null) {
          eventMismatches += 1;
        }
        continue;
      }

      if (capturedEvents[k] === null || fullOutput === null) {
        eventMismatches += 1;
        continue;
      }

      const fullLabel = full.output_labels[fullOutput];
      const eventPair = [
        Math.floor(capturedEvents[k] / 3),
        capturedEvents[k] % 3,
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
      if (base.output_labels[expected].key !== fullCarryKey) {
        carryMismatches += 1;
      }
    }

    wordsChecked += 1;
  }
}

if (outputMismatches || eventMismatches || carryMismatches) {
  throw new Error(JSON.stringify({
    outputMismatches,
    eventMismatches,
    carryMismatches,
  }));
}

const eventTransitionCounts = [0, 0, 0];
for (const row of eventMasks) {
  for (const mask of row) {
    for (let k = 0; k <= maxShift; k += 1) {
      if (mask & (1 << k)) eventTransitionCounts[k] += 1;
    }
  }
}

const result = {
  description:
    "Reachable product of three buffer-relative first-common-reset carry machines, " +
    "for the word and its suffixes after dropping one or two initial symbols.",
  alphabet: {
    size: alphabetSize,
    encoding: "symbol = 3*x + y, x,y in {0,1,2}",
  },
  source_artifacts: {
    buffer_relative:
      "im-results/agent48-623-tight-window/ResetPostStateDFA_BufferRelative.json",
    original_output:
      "im-results/agent49-parity623/ResetPostStateDFA.json",
  },
  semantics: {
    offsets: [0, 1, 2],
    state_map: "[consumed-prefix-count-capped-at-2, copy0, copy1, copy2]",
    outputs:
      "For each offset, the first-reset joint L/R carry-profile label, or null.",
    event_masks:
      "Bit k is set on the symbol that first completes a reset in suffix k.",
    event_symbol:
      "For a set bit and input symbol z, previous_pair=[floor(z/3), z mod 3].",
    consumer:
      "Capture each event symbol when emitted. The carry-profile label plus that " +
      "symbol reconstructs the corresponding original 54-label reset output.",
  },
  state_count: states.length,
  initial_state: initialState,
  carry_labels: base.output_labels.map(label => label.key),
  states,
  transitions,
  outputs,
  event_masks: eventMasks,
  minimization: {
    method: "reachable Moore/Mealy partition refinement",
    partition_counts: partitionCounts,
    minimized_state_count: minimizedStateCount,
  },
  validation: {
    transitions_checked: states.length * alphabetSize,
    event_transition_counts_by_offset: eventTransitionCounts,
    exhaustive_words_through_length: 6,
    exhaustive_words_checked: wordsChecked,
    output_mismatches: outputMismatches,
    event_symbol_mismatches: eventMismatches,
    carry_label_mismatches: carryMismatches,
  },
};

fs.writeFileSync(outputPath, JSON.stringify(result, null, 2) + "\n");

const summary = {
  outputPath,
  state_count: result.state_count,
  transitions_checked: result.validation.transitions_checked,
  minimized_state_count: result.minimization.minimized_state_count,
  partition_counts: result.minimization.partition_counts,
  exhaustive_words_checked: result.validation.exhaustive_words_checked,
  output_mismatches: outputMismatches,
  event_symbol_mismatches: eventMismatches,
  carry_label_mismatches: carryMismatches,
};
process.stdout.write(JSON.stringify(summary, null, 2) + "\n");
