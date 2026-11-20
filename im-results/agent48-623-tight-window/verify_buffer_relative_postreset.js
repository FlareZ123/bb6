#!/usr/bin/env node
"use strict";
const fs = require("node:fs");
const path = require("node:path");

const root = path.resolve(__dirname, "../..");
const source = JSON.parse(fs.readFileSync(path.join(root, "im-results/agent49-parity623/ResetPostStateDFA.json"), "utf8"));
const compressed = JSON.parse(fs.readFileSync(path.join(__dirname, "ResetPostStateDFA_BufferRelative.json"), "utf8"));

function outputKey(label, withLength) {
  const carry = label.L_final.carry.join(",") + "|" + label.R_final.carry.join(",");
  return withLength ? carry + "|" + label.witness_length : carry;
}

function verifyQuotient(original, compact, withLength) {
  const map = compact.state_map;
  if (map.length !== original.transitions.length) throw new Error("state-map length mismatch");
  if (map[original.initial_state] !== compact.initial_state) throw new Error("initial-state quotient mismatch");
  const labelIds = new Map(compact.output_labels.map((label, i) => [label.key, i]));
  for (let s = 0; s < original.transitions.length; s += 1) {
    const q = map[s];
    const oldOutput = original.outputs[s];
    const expectedOutput = oldOutput === null ? null : labelIds.get(outputKey(original.output_labels[oldOutput], withLength));
    if (compact.outputs[q] !== expectedOutput) throw new Error("output mismatch at source state " + s);
    for (let z = 0; z < 9; z += 1) {
      if (map[original.transitions[s][z]] !== compact.transitions[q][z]) {
        throw new Error("transition mismatch at source state " + s + ", symbol " + z);
      }
    }
  }
  return {sourceStates: original.transitions.length, quotientStates: compact.state_count, sourceLabels: original.output_labels.length, quotientLabels: compact.output_labels.length};
}

function run(machine, word) {
  let state = machine.initial_state;
  for (const symbol of word) state = machine.transitions[state][symbol];
  const output = machine.outputs[state];
  return output === null ? null : machine.output_labels[output];
}

function runOriginalWithFirstOutput(machine, word) {
  let state = machine.initial_state;
  let first = null;
  const buffer = [0, 0];
  for (let i = 0; i < word.length; i += 1) {
    buffer.push(word[i]);
    if (buffer.length > 5) buffer.shift();
    state = machine.transitions[state][word[i]];
    if (first === null && machine.outputs[state] !== null) {
      first = {index: i, symbol: word[i], label: machine.output_labels[machine.outputs[state]], buffer: buffer.slice()};
    }
  }
  const output = machine.outputs[state];
  return {label: output === null ? null : machine.output_labels[output], first};
}

function decodeWord(code, length) {
  const word = new Array(length);
  for (let i = length - 1; i >= 0; i -= 1) {
    word[i] = code % 9;
    code = Math.floor(code / 9);
  }
  return word;
}

const pairQuotient = verifyQuotient(source.post_reset_pair, compressed.pair_carry_only, false);
const pairLengthQuotient = verifyQuotient(source.post_reset_pair_and_length, compressed.pair_carry_and_length, true);
let wordsChecked = 0;
let pairMismatches = 0;
let pairLengthMismatches = 0;
let previousPairRecoveryMismatches = 0;
let secondSymbolRecoveryMismatches = 0;

for (let length = 0; length <= 6; length += 1) {
  for (let code = 0; code < 9 ** length; code += 1) {
    const word = decodeWord(code, length);
    const pairOriginal = runOriginalWithFirstOutput(source.post_reset_pair, word);
    const pairCompact = run(compressed.pair_carry_only, word);
    const pairExpected = pairOriginal.label === null ? null : outputKey(pairOriginal.label, false);
    if ((pairCompact === null ? null : pairCompact.key) !== pairExpected) pairMismatches += 1;
    if (pairOriginal.first !== null) {
      const [x, y] = pairOriginal.first.label.L_final.previous_pair;
      if (pairOriginal.first.symbol !== 3 * x + y) previousPairRecoveryMismatches += 1;
    }

    const lengthOriginal = runOriginalWithFirstOutput(source.post_reset_pair_and_length, word);
    const lengthCompact = run(compressed.pair_carry_and_length, word);
    const lengthExpected = lengthOriginal.label === null ? null : outputKey(lengthOriginal.label, true);
    if ((lengthCompact === null ? null : lengthCompact.key) !== lengthExpected) pairLengthMismatches += 1;
    if (lengthOriginal.first !== null) {
      const [x, y] = lengthOriginal.first.label.L_final.previous_pair;
      if (lengthOriginal.first.symbol !== 3 * x + y) previousPairRecoveryMismatches += 1;
      const witnessLength = lengthOriginal.first.label.witness_length;
      const secondWordIndex = lengthOriginal.first.index - witnessLength + 2;
      const bufferIndex = 6 - witnessLength;
      if (
        lengthOriginal.first.buffer.length !== 5 ||
        bufferIndex < 0 || bufferIndex >= 5 ||
        secondWordIndex < 0 || secondWordIndex >= word.length ||
        lengthOriginal.first.buffer[bufferIndex] !== word[secondWordIndex]
      ) secondSymbolRecoveryMismatches += 1;
    }
    wordsChecked += 1;
  }
}

if (pairMismatches || pairLengthMismatches || previousPairRecoveryMismatches || secondSymbolRecoveryMismatches) {
  throw new Error("finite-word quotient validation failed");
}
console.log(JSON.stringify({
  pairQuotient,
  pairLengthQuotient,
  wordsChecked,
  pairMismatches,
  pairLengthMismatches,
  previousPairRecoveryMismatches,
  secondSymbolRecoveryMismatches
}, null, 2));
