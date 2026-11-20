#!/usr/bin/env node
// Reproduce the #623 S-indexed reset-window diagnostic with the tighter
// source-derived correction envelope B=max(34*ellS+122,36*ellS+88).
// The recurrence is the same explicit JS transcription used by
// agent1-machine623-3euclidean-correction-bounds/synchronizing_word_scan.js.
// This is a finite diagnostic, not an original-source or all-time proof.

const fs = require("node:fs");
const path = require("node:path");

const dfaPath = path.join(
  process.cwd(),
  "im-results/agent32-623-phase-automaton/ResetPatternDFA.json"
);
const dfa = JSON.parse(fs.readFileSync(dfaPath, "utf8"));
const transitions = dfa.transitions;
const accepting = new Set(dfa.accepting_states);

function evalA(a, k, m) {
  while (true) {
    if (k % 3n === 2n) return [a + 1n, k / 3n, m];
    if (a === 0n) return k % 3n === 0n ? null : [0n, k / 3n, m];
    if (k % 3n === 0n) return [a - 1n, k / 3n, m + 2n];
    k = k / 3n;
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
  if (a === 0n)
    return d % 2n === 1n ? drainB(d + 1n, 2n, 2n) : [d, 7n];
  if (d % 2n === 1n && a >= d + 5n)
    return drainB(a - d - 5n, d + 3n, 5n);
  if (d % 2n === 0n && a >= d + 3n)
    return drainB(a - d - 2n, d + 2n, 2n);
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

function ellOfS(S) {
  let ell = 0;
  let power = 1n;
  while ((power - 1n) / 2n < S + 3n) {
    ell += 1;
    power *= 3n;
  }
  return ell;
}

function digitsMod3(x, length) {
  const modulus = 3n ** BigInt(length);
  let n = x % modulus;
  if (n < 0n) n += modulus;
  const digits = [];
  for (let i = 0; i < length; i += 1) {
    digits.push(Number(n % 3n));
    n /= 3n;
  }
  return digits;
}

function scanWindow(B, z, q) {
  let k = 0;
  let power = 1;
  while (power <= B) {
    power *= 3;
    k += 1;
  }
  let j = 0;
  let power3 = 1n;
  const target = BigInt(B) ** 3n;
  while (power3 <= target) {
    power3 *= 3n;
    j += 1;
  }

  const xDigits = digitsMod3(z, j);
  const yDigits = digitsMod3(6n * q, j);
  let state = dfa.initial_state;
  let firstAcceptEnd = null;
  let wordLength = 0;

  for (let i = k + 2; i < j - 2; i += 1) {
    state = transitions[state][xDigits[i] * 3 + yDigits[i]];
    wordLength += 1;
    if (firstAcceptEnd === null && accepting.has(state)) {
      firstAcceptEnd = wordLength;
    }
  }

  return {
    k,
    j,
    wordLength,
    firstAcceptEnd,
    accepted: accepting.has(state),
  };
}

const maxStep = Number(process.argv[2] || 10000);
let a = 0n;
let d = 7n;
let states = 0;
let oldFailures = 0;
let newFailures = 0;
let firstOldFailure = null;
let firstNewFailure = null;
let changedK = 0;
let changedJ = 0;
let oldMinusNewK = {};
let oldMinusNewJ = {};
let oldFirstEndHistogram = {};
let newFirstEndHistogram = {};
let oldLength = [Infinity, 0];
let newLength = [Infinity, 0];
let firstChanged = [];

for (let index = 0; index <= maxStep; index += 1) {
  if (index >= 33) {
    const { q, S, z } = stateData(a, d);
    const ell = ellOfS(S);
    const oldB = Math.max(34 * ell + 140, 36 * ell + 88);
    const newB = Math.max(34 * ell + 122, 36 * ell + 88);
    if (newB > oldB) throw new Error("tightened bound exceeds old bound");

    const oldWindow = scanWindow(oldB, z, q);
    const newWindow = scanWindow(newB, z, q);

    if (!oldWindow.accepted) {
      oldFailures += 1;
      if (firstOldFailure === null) firstOldFailure = index;
    }
    if (!newWindow.accepted) {
      newFailures += 1;
      if (firstNewFailure === null) firstNewFailure = index;
    }

    if (oldWindow.k !== newWindow.k) changedK += 1;
    if (oldWindow.j !== newWindow.j) changedJ += 1;

    const dk = String(oldWindow.k - newWindow.k);
    const dj = String(oldWindow.j - newWindow.j);
    oldMinusNewK[dk] = (oldMinusNewK[dk] || 0) + 1;
    oldMinusNewJ[dj] = (oldMinusNewJ[dj] || 0) + 1;

    oldLength[0] = Math.min(oldLength[0], oldWindow.wordLength);
    oldLength[1] = Math.max(oldLength[1], oldWindow.wordLength);
    newLength[0] = Math.min(newLength[0], newWindow.wordLength);
    newLength[1] = Math.max(newLength[1], newWindow.wordLength);

    const oldEnd = String(oldWindow.firstAcceptEnd ?? "none");
    const newEnd = String(newWindow.firstAcceptEnd ?? "none");
    oldFirstEndHistogram[oldEnd] = (oldFirstEndHistogram[oldEnd] || 0) + 1;
    newFirstEndHistogram[newEnd] = (newFirstEndHistogram[newEnd] || 0) + 1;

    if (
      firstChanged.length < 10 &&
      (oldWindow.k !== newWindow.k ||
        oldWindow.j !== newWindow.j ||
        !newWindow.accepted)
    ) {
      firstChanged.push({
        index,
        ell,
        oldB,
        newB,
        oldWindow,
        newWindow,
      });
    }
    states += 1;
  }

  if (index === maxStep) break;
  const next = highLevelNext(a, d);
  if (next === null) break;
  [a, d] = next;
}

const summary = {
  maxStep,
  states,
  oldFailures,
  firstOldFailure,
  newFailures,
  firstNewFailure,
  changedK,
  changedJ,
  oldMinusNewK,
  oldMinusNewJ,
  oldWindowLengthRange: oldLength,
  newWindowLengthRange: newLength,
  oldFirstAcceptEndHistogram: oldFirstEndHistogram,
  newFirstAcceptEndHistogram: newFirstEndHistogram,
  firstChanged,
};

console.log(JSON.stringify(summary, null, 2));
if (oldFailures !== 0 || newFailures !== 0) process.exitCode = 1;
