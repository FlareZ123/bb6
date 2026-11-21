#!/usr/bin/env node
"use strict";

// Shift-aware reset-window diagnostic for the #623 root.
// The root recurrence below is mirrored from the existing source-faithful
// scan. This script is computational evidence, not a proof of the recurrence.

const fs = require("node:fs");
const path = require("node:path");
const assert = require("node:assert/strict");

const dfaPath = path.join(__dirname, "../agent32-623-phase-automaton/ResetPatternDFA.json");
const dfa = JSON.parse(fs.readFileSync(dfaPath, "utf8"));
const transitions = dfa.transitions;
const accepting = new Set(dfa.accepting_states);
const initial = dfa.initial_state;

function decodeBase9(code, length) {
  const word = new Array(length);
  for (let i = length - 1; i >= 0; i--) {
    word[i] = code % 9;
    code = Math.floor(code / 9);
  }
  return word;
}

function accepted(word) {
  let state = initial;
  for (const symbol of word) state = transitions[state][symbol];
  return accepting.has(state);
}

function isMinimalResetWord(word) {
  if (!accepted(word)) return false;
  for (let length = 3; length < word.length; length++) {
    for (let start = 0; start + length <= word.length; start++) {
      if (accepted(word.slice(start, start + length))) return false;
    }
  }
  return true;
}

function buildCarryTransducer(branch) {
  const amin = branch === "L" ? -2 : -4;
  const amax = branch === "L" ? 2 : 1;
  const acount = amax - amin + 1;
  const count = 9 * acount * 5;
  const next = new Int16Array(count * 9);
  const outputX = new Int8Array(count * 9);
  next.fill(-1);

  for (let xp = 0; xp < 3; xp++) {
    for (let yp = 0; yp < 3; yp++) {
      for (let a = amin; a <= amax; a++) {
        for (let b = -2; b <= 2; b++) {
          const state = (((xp * 3 + yp) * acount + (a - amin)) * 5 + (b + 2));
          for (let x = 0; x < 3; x++) {
            for (let y = 0; y < 3; y++) {
              const tx = branch === "L" ? x - yp + a : -x - xp - yp + a;
              const ty = branch === "L" ? yp + b : xp + yp + b;
              const digit = ((tx % 3) + 3) % 3;
              const an = Math.floor(tx / 3);
              const bn = Math.floor(ty / 3);
              assert(an >= amin && an <= amax, "carry rectangle is not closed in " + branch);
              assert(bn >= -2 && bn <= 2, "carry rectangle is not closed in " + branch);
              const index = state * 9 + x * 3 + y;
              next[index] = (((x * 3 + y) * acount + (an - amin)) * 5 + (bn + 2));
              outputX[index] = digit;
            }
          }
        }
      }
    }
  }

  for (const n of next) assert(n >= 0, "incomplete transition table for " + branch);
  return { count, next, outputX };
}

const transducer = {
  L: buildCarryTransducer("L"),
  R: buildCarryTransducer("R")
};

// A pattern is shift-robust for a branch iff, for every initial carry state,
// the x-output digits after dropping the first pattern digit, followed by
// one arbitrary next input symbol, contain both a nonzero and a non-two digit.
function isShiftRobust(machine, word) {
  const seenNonzero = new Uint8Array(machine.count);
  const seenNotTwo = new Uint8Array(machine.count);
  let commonFinal = -1;

  for (let start = 0; start < machine.count; start++) {
    let state = start;
    let nonzero = 0;
    let notTwo = 0;
    for (let i = 0; i < word.length; i++) {
      const index = state * 9 + word[i];
      const output = machine.outputX[index];
      if (i >= 1) {
        if (output !== 0) nonzero = 1;
        if (output !== 2) notTwo = 1;
      }
      state = machine.next[index];
    }
    if (commonFinal < 0) commonFinal = state;
    else assert.equal(state, commonFinal, "reset word did not synchronize " + "the " + machine.count + "-state transducer");
    seenNonzero[start] = nonzero;
    seenNotTwo[start] = notTwo;
  }

  for (let symbol = 0; symbol < 9; symbol++) {
    const index = commonFinal * 9 + symbol;
    const output = machine.outputX[index];
    const addsNonzero = output !== 0;
    const addsNotTwo = output !== 2;
    for (let start = 0; start < machine.count; start++) {
      if (!(seenNonzero[start] || addsNonzero)) return false;
      if (!(seenNotTwo[start] || addsNotTwo)) return false;
    }
  }
  return true;
}

const patterns = new Map();
const robust = { L: new Set(), R: new Set() };
const patternCountsByLength = {};

for (let length = 3; length <= 6; length++) {
  patternCountsByLength[length] = { total: 0, robustL: 0, robustR: 0 };
  for (let code = 0; code < 9 ** length; code++) {
    const word = decodeBase9(code, length);
    if (!isMinimalResetWord(word)) continue;
    const key = word.join(",");
    patterns.set(key, word);
    patternCountsByLength[length].total++;
    if (isShiftRobust(transducer.L, word)) {
      robust.L.add(key);
      patternCountsByLength[length].robustL++;
    }
    if (isShiftRobust(transducer.R, word)) {
      robust.R.add(key);
      patternCountsByLength[length].robustR++;
    }
  }
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
    const result = evalA(a, b - 1n, d + 2n * b + 3n);
    if (result === null || result[1] >= b) return null;
    [a, b, d] = result;
  }
  return [a, d];
}

// Exact source-faithful recurrence mirror used by the existing root scans.
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

function stateData(a, d) {
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
  return { q, S: a + d, z: 2n * g - gamma, sector };
}

function sourceBranch(a, d) {
  if (d % 2n === 1n && a >= d + 5n) return "L";
  if (d % 2n === 0n && a >= d + 3n) return "L";
  if (a % 2n === 0n && d % 2n === 1n) return "R";
  if (a % 2n === 0n && d % 2n === 0n) return "R";
  return null;
}

function ellOfS(S) {
  let ell = 0;
  let power = 1n;
  while ((power - 1n) / 2n < S + 3n) {
    ell++;
    power *= 3n;
  }
  return ell;
}

// Conservative source mass window: max(34 ell + 140, 36 ell + 88).
function windowBound(S) {
  const ell = BigInt(ellOfS(S));
  const a = 34n * ell + 140n;
  const b = 36n * ell + 88n;
  return a > b ? a : b;
}

function windowIndices(B) {
  let k = 0;
  let power = 1n;
  while (power <= B) {
    power *= 3n;
    k++;
  }
  let j = 0;
  power = 1n;
  const target = B ** 3n;
  while (power <= target) {
    power *= 3n;
    j++;
  }
  return { k, j };
}

function digitsMod3(value, length) {
  const modulus = 3n ** BigInt(length);
  let n = value % modulus;
  if (n < 0n) n += modulus;
  const digits = [];
  for (let i = 0; i < length; i++) {
    digits.push(Number(n % 3n));
    n /= 3n;
  }
  return digits;
}

function scanTransition(index, a, d, nextState) {
  const current = stateData(a, d);
  const target = stateData(nextState[0], nextState[1]);
  const currentWindow = windowIndices(windowBound(current.S));
  const targetWindow = windowIndices(windowBound(target.S));
  const deltaK = targetWindow.k - currentWindow.k;
  const deltaJ = targetWindow.j - currentWindow.j;

  assert([0, 1].includes(deltaK), "unexpected low-end shift at transition " + index);
  assert([0, 1, 2, 3].includes(deltaJ), "unexpected high-end shift at transition " + index);
  if (deltaK === 1) assert(deltaJ >= 1, "low shift without high extension at transition " + index);

  const xDigits = digitsMod3(current.z, currentWindow.j);
  const yDigits = digitsMod3(6n * current.q, currentWindow.j);
  const word = [];
  for (let i = currentWindow.k + 2; i < currentWindow.j - 2; i++) {
    word.push(xDigits[i] * 3 + yDigits[i]);
  }
  assert(word.length >= 8 && word.length <= 16, "unexpected window length at transition " + index);

  const branch = current.sector === "LO" || current.sector === "LE" ? "L" : "R";
  assert.equal(sourceBranch(a, d), branch, "sector/source branch mismatch at transition " + index);

  const found = [];
  for (let start = 0; start <= word.length - 3; start++) {
    for (let length = 3; length <= 6 && start + length <= word.length; length++) {
      const symbols = word.slice(start, start + length);
      const key = symbols.join(",");
      if (patterns.has(key)) found.push({ start, length, key });
    }
  }

  const first = found.length ? found[0] : null;
  const selected = found.find((w) =>
    deltaK === 0 || w.start >= 1 || (w.start === 0 && robust[branch].has(w.key))
  ) || null;

  if (selected && deltaK === 1 && selected.start === 0) {
    assert(word.length - selected.length >= 1, "no suffix symbol after left-edge reset at transition " + index);
  }

  return {
    index,
    sector: current.sector,
    branch,
    deltaK,
    deltaJ,
    windowLength: word.length,
    first,
    firstRobustAtLeft: first !== null && first.start === 0 && robust[branch].has(first.key),
    selected,
    safe: selected !== null
  };
}

const summary = {
  minimalPatterns: patterns.size,
  patternCountsByLength,
  shiftRobustPatterns: { L: robust.L.size, R: robust.R.size },
  testedTransitions: 0,
  shiftPairs: {},
  branches: { L: 0, R: 0 },
  windowLength: { min: Infinity, max: 0 },
  firstWitness: { atLeft: 0, later: 0, robustAtLeft: 0, nonrobustAtLeft: 0 },
  shiftOneWitness: { robustAtLeft: 0, later: 0 },
  failures: [],
  shiftOneCases: []
};

let a = 0n;
let d = 7n;
for (let index = 0; index <= 10000; index++) {
  const nextState = highLevelNext(a, d);
  if (index >= 33 && nextState !== null) {
    const result = scanTransition(index, a, d, nextState);
    summary.testedTransitions++;
    const pair = result.deltaK + "," + result.deltaJ;
    summary.shiftPairs[pair] = (summary.shiftPairs[pair] || 0) + 1;
    summary.branches[result.branch]++;
    summary.windowLength.min = Math.min(summary.windowLength.min, result.windowLength);
    summary.windowLength.max = Math.max(summary.windowLength.max, result.windowLength);

    if (result.first && result.first.start === 0) {
      summary.firstWitness.atLeft++;
      if (result.firstRobustAtLeft) summary.firstWitness.robustAtLeft++;
      else summary.firstWitness.nonrobustAtLeft++;
    } else if (result.first) {
      summary.firstWitness.later++;
    }

    if (result.deltaK === 1) {
      if (result.selected && result.selected.start === 0) summary.shiftOneWitness.robustAtLeft++;
      else if (result.selected && result.selected.start >= 1) summary.shiftOneWitness.later++;
      summary.shiftOneCases.push({
        index,
        sector: result.sector,
        branch: result.branch,
        deltaJ: result.deltaJ,
        windowLength: result.windowLength,
        first: result.first,
        selected: result.selected
      });
    }

    if (!result.safe) summary.failures.push(result);
  }

  if (index === 10000 || nextState === null) break;
  [a, d] = nextState;
}

assert.equal(summary.minimalPatterns, 8088, "unexpected minimal reset language size");
assert.equal(summary.testedTransitions, 9968, "unexpected root trace length");
assert.equal(summary.failures.length, 0, "shift-aware reset criterion failed");

console.log(JSON.stringify(summary, null, 2));
