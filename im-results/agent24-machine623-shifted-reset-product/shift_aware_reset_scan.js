#!/usr/bin/env node
"use strict";

// Shift-aware reset/output diagnostic for the #623 root.
// The root recurrence is mirrored from the existing source-faithful scan.
// This is finite computational evidence, not an all-time proof.

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
  for (let state = 0; state < count; state++) {
    const outputs = new Set();
    for (let symbol = 0; symbol < 9; symbol++) outputs.add(outputX[state * 9 + symbol]);
    assert.equal(outputs.size, 3, "next x-output is not surjective in " + branch);
  }
  return { amin, amax, acount, count, next, outputX };
}

const machine = { L: buildCarryTransducer("L"), R: buildCarryTransducer("R") };

function isDropOneRobust(transducer, word) {
  const seenNonzero = new Uint8Array(transducer.count);
  const seenNotTwo = new Uint8Array(transducer.count);
  let commonFinal = -1;

  for (let start = 0; start < transducer.count; start++) {
    let state = start;
    let nonzero = 0;
    let notTwo = 0;
    for (let i = 0; i < word.length; i++) {
      const index = state * 9 + word[i];
      const output = transducer.outputX[index];
      if (i >= 1) {
        if (output !== 0) nonzero = 1;
        if (output !== 2) notTwo = 1;
      }
      state = transducer.next[index];
    }
    if (commonFinal < 0) commonFinal = state;
    else assert.equal(state, commonFinal, "reset word failed to synchronize a transducer");
    seenNonzero[start] = nonzero;
    seenNotTwo[start] = notTwo;
  }

  // Equivalent to suffix nonmonochromaticity: every state can emit any
  // next x-digit, so a monochromatic suffix can be kept monochromatic.
  for (let symbol = 0; symbol < 9; symbol++) {
    const index = commonFinal * 9 + symbol;
    const output = transducer.outputX[index];
    for (let start = 0; start < transducer.count; start++) {
      if (!(seenNonzero[start] || output !== 0)) return false;
      if (!(seenNotTwo[start] || output !== 2)) return false;
    }
  }
  return true;
}

const patterns = new Map();
const dropOneRobust = { L: new Set(), R: new Set() };
const patternCountsByLength = {};

for (let length = 3; length <= 6; length++) {
  patternCountsByLength[length] = { total: 0, robustL: 0, robustR: 0 };
  for (let code = 0; code < 9 ** length; code++) {
    const word = decodeBase9(code, length);
    if (!isMinimalResetWord(word)) continue;
    const key = word.join(",");
    patterns.set(key, word);
    patternCountsByLength[length].total++;
    if (isDropOneRobust(machine.L, word)) {
      dropOneRobust.L.add(key);
      patternCountsByLength[length].robustL++;
    }
    if (isDropOneRobust(machine.R, word)) {
      dropOneRobust.R.add(key);
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

function drainBStats(a, b, d) {
  let r = 0;
  while (b !== 0n) {
    const result = evalA(a, b - 1n, d + 2n * b + 3n);
    r++;
    if (result === null || result[1] >= b) return null;
    [a, b, d] = result;
  }
  return { a, d, r };
}

function drainB(a, b, d) {
  const result = drainBStats(a, b, d);
  return result === null ? null : [result.a, result.d];
}

// Source-faithful high-level recurrence mirror used by the existing scans.
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

// Exact drain statistics used by the source output-side branch threshold.
// D is the signed first-counter drop from the sector baseline; r counts
// outer drain iterations (the initial RE evalA contributes to D, not r).
function sourceDrainStats(a, d) {
  let sector, initialA, result;
  if (a >= d) {
    if (d % 2n === 1n) {
      sector = "LO";
      initialA = a - d - 5n;
      result = drainBStats(initialA, d + 3n, 5n);
    } else {
      sector = "LE";
      initialA = a - d - 2n;
      result = drainBStats(initialA, d + 2n, 2n);
    }
  } else if (d % 2n === 1n) {
    sector = "RO";
    initialA = d + 4n - a;
    result = drainBStats(initialA, a - 1n, 3n);
  } else {
    sector = "RE";
    initialA = d + 1n - a;
    const first = evalA(initialA, a, 2n * a + 5n);
    if (first === null) return null;
    result = drainBStats(...first);
  }
  if (result === null) return null;
  return { sector, D: initialA - result.a, r: result.r };
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
  return { q, S: a + d, z: 2n * g - gamma, sector, g };
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
  const left = 34n * ell + 140n;
  const right = 36n * ell + 88n;
  return left > right ? left : right;
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

function modEuclid(value, modulus) {
  const remainder = value % modulus;
  return remainder < 0n ? remainder + modulus : remainder;
}

function floorDiv(value, divisor) {
  let quotient = value / divisor;
  if (value % divisor < 0n) quotient -= 1n;
  return quotient;
}

function digitsMod3(value, length) {
  let n = modEuclid(value, 3n ** BigInt(length));
  const digits = [];
  for (let i = 0; i < length; i++) {
    digits.push(Number(n % 3n));
    n /= 3n;
  }
  return digits;
}

function sourceCarries(x, y, C, F, K, branch) {
  const threeK = 3n * K;
  const xLow1 = modEuclid(x, threeK);
  const xLow0 = modEuclid(x, K);
  const yLow = modEuclid(y, K);
  let a, b;
  if (branch === "L") {
    a = floorDiv(xLow1 - 3n * yLow + C, threeK);
    b = floorDiv(3n * yLow + F, threeK);
  } else {
    a = floorDiv(-xLow1 - 3n * xLow0 - 3n * yLow + C, threeK);
    b = floorDiv(3n * xLow0 + 3n * yLow + F, threeK);
  }
  return {
    xp: Number(modEuclid(floorDiv(x, K), 3n)),
    yp: Number(modEuclid(floorDiv(y, K), 3n)),
    a: Number(a),
    b: Number(b)
  };
}

function stateId(transducer, state) {
  assert(state.a >= transducer.amin && state.a <= transducer.amax,
    "source a-carry outside full " + transducer.amin + ".." + transducer.amax + " rectangle: " + state.a);
  assert(state.b >= -2 && state.b <= 2, "source b-carry outside full rectangle: " + state.b);
  return (((state.xp * 3 + state.yp) * transducer.acount + (state.a - transducer.amin)) * 5 + (state.b + 2));
}

function runPattern(transducer, initialState, word) {
  let state = stateId(transducer, initialState);
  const output = [];
  for (const symbol of word) {
    const index = state * 9 + symbol;
    output.push(transducer.outputX[index]);
    state = transducer.next[index];
    assert(state >= 0, "missing transducer edge");
  }
  return output;
}

function nonmonochromatic(digits) {
  return digits.some((digit) => digit !== 0) && digits.some((digit) => digit !== 2);
}

const summary = {
  minimalPatterns: patterns.size,
  patternCountsByLength,
  dropOneRobustPatterns: { L: dropOneRobust.L.size, R: dropOneRobust.R.size },
  testedTransitions: 0,
  shiftPairs: {},
  affineBranches: { L: 0, R: 0 },
  windowLength: { min: Infinity, max: 0 },
  correctionBoundFailures: 0,
  carryRectangleFailures: 0,
  affineDigitMismatches: 0,
  windowsWithoutReset: 0,
  windowsWithoutSafeActualWitness: 0,
  firstResetAtLeft: 0,
  firstResetAtLeftSuffixGood: 0,
  firstResetAtLeftSuffixBad: 0,
  selectedWitness: { atLeft: 0, later: 0 },
  shiftOneCases: [],
  signThresholdDisagreements: 0,
  DRange: { min: Infinity, max: -Infinity },
  rRange: { min: Infinity, max: -Infinity }
};

let a = 0n;
let d = 7n;
for (let index = 0; index <= 10000; index++) {
  const nextState = highLevelNext(a, d);
  if (index >= 33 && nextState !== null) {
    const current = stateData(a, d);
    const target = stateData(nextState[0], nextState[1]);
    const drainStats = sourceDrainStats(a, d);
    assert(drainStats !== null, "missing source drain statistics at transition " + index);
    assert.equal(drainStats.sector, current.sector, "source sector/statistics mismatch at transition " + index);
    const thresholdOffset = { LO: 19n, LE: 10n, RO: -4n, RE: 4n }[drainStats.sector];
    const threshold = 3n * drainStats.D + 2n * BigInt(drainStats.r) + thresholdOffset;
    // Exact source output-side decision from RootRayGapCocycle.md:
    // left iff g >= 3D + 2r + c_T. The sign(g) simplification is not used.
    const branch = current.g >= threshold ? "L" : "R";
    if ((current.g > 0n ? "L" : "R") !== branch) summary.signThresholdDisagreements++;
    summary.DRange.min = Math.min(summary.DRange.min, Number(drainStats.D));
    summary.DRange.max = Math.max(summary.DRange.max, Number(drainStats.D));
    summary.rRange.min = Math.min(summary.rRange.min, drainStats.r);
    summary.rRange.max = Math.max(summary.rRange.max, drainStats.r);
    const transducer = machine[branch];

    const B = windowBound(current.S);
    const Bnext = windowBound(target.S);
    const currentWindow = windowIndices(B);
    const targetWindow = windowIndices(Bnext);
    const deltaK = targetWindow.k - currentWindow.k;
    const deltaJ = targetWindow.j - currentWindow.j;
    assert([0, 1].includes(deltaK), "unexpected low-end shift at transition " + index);
    assert([0, 1, 2, 3].includes(deltaJ), "unexpected high-end shift at transition " + index);
    if (deltaK === 1) assert(deltaJ >= 1, "low shift without high extension at transition " + index);

    const x = current.z;
    const y = 6n * current.q;
    const xNext = target.z;
    const yNext = 6n * target.q;
    const C = branch === "L" ? xNext - x + 3n * y : xNext + 4n * x + 3n * y;
    const F = branch === "L" ? yNext - 3n * y : yNext - 3n * x - 3n * y;
    if ((C < 0n ? -C : C) > B || (F < 0n ? -F : F) > B) {
      summary.correctionBoundFailures++;
    }

    const xDigits = digitsMod3(x, currentWindow.j);
    const yDigits = digitsMod3(y, currentWindow.j);
    const nextXDigits = digitsMod3(xNext, targetWindow.j);
    const word = [];
    for (let i = currentWindow.k + 2; i < currentWindow.j - 2; i++) {
      word.push(xDigits[i] * 3 + yDigits[i]);
    }
    assert(word.length >= 8 && word.length <= 16, "unexpected S-window length at transition " + index);
    summary.testedTransitions++;
    summary.affineBranches[branch]++;
    summary.windowLength.min = Math.min(summary.windowLength.min, word.length);
    summary.windowLength.max = Math.max(summary.windowLength.max, word.length);
    const shiftPair = deltaK + "," + deltaJ;
    summary.shiftPairs[shiftPair] = (summary.shiftPairs[shiftPair] || 0) + 1;

    const found = [];
    for (let start = 0; start <= word.length - 3; start++) {
      for (let length = 3; length <= 6 && start + length <= word.length; length++) {
        const symbols = word.slice(start, start + length);
        const key = symbols.join(",");
        if (patterns.has(key)) found.push({ start, length, key, symbols });
      }
    }
    if (found.length === 0) summary.windowsWithoutReset++;

    let selected = null;
    for (const witness of found) {
      const K = 3n ** BigInt(currentWindow.k + 1 + witness.start);
      const carries = sourceCarries(x, y, C, F, K, branch);
      let output;
      try {
        output = runPattern(transducer, carries, witness.symbols);
      } catch (error) {
        summary.carryRectangleFailures++;
        continue;
      }

      const drop = deltaK === 1 && witness.start === 0 ? 1 : 0;
      let matches = true;
      for (let i = 0; i < witness.length; i++) {
        const position = currentWindow.k + 2 + witness.start + i;
        if (position >= nextXDigits.length || output[i] !== nextXDigits[position]) {
          matches = false;
          break;
        }
      }
      if (!matches) summary.affineDigitMismatches++;

      if (nonmonochromatic(output.slice(drop))) {
        selected = { ...witness, drop };
        break;
      }
    }

    const first = found[0] || null;
    if (first && first.start === 0) {
      summary.firstResetAtLeft++;
      const K = 3n ** BigInt(currentWindow.k + 1);
      const carries = sourceCarries(x, y, C, F, K, branch);
      const output = runPattern(transducer, carries, first.symbols);
      if (nonmonochromatic(output.slice(deltaK === 1 ? 1 : 0))) {
        summary.firstResetAtLeftSuffixGood++;
      } else {
        summary.firstResetAtLeftSuffixBad++;
      }
    }

    if (selected === null) {
      summary.windowsWithoutSafeActualWitness++;
    } else if (selected.start === 0) {
      summary.selectedWitness.atLeft++;
    } else {
      summary.selectedWitness.later++;
    }

    if (deltaK === 1) {
      summary.shiftOneCases.push({
        index,
        branch,
        g: String(current.g),
        deltaJ,
        first: first ? { start: first.start, length: first.length, word: first.symbols } : null,
        selected: selected ? { start: selected.start, length: selected.length, word: selected.symbols } : null
      });
    }
  }

  if (index === 10000 || nextState === null) break;
  [a, d] = nextState;
}

assert.equal(summary.minimalPatterns, 8088, "unexpected minimal reset language size");
assert.equal(summary.testedTransitions, 9968, "unexpected root trace length");
assert.equal(summary.correctionBoundFailures, 0, "source correction bound failed on finite trace");
assert.equal(summary.carryRectangleFailures, 0, "actual source carry escaped full rectangle");
assert.equal(summary.affineDigitMismatches, 0, "transducer output disagrees with actual successor x-digits");
assert.equal(summary.windowsWithoutReset, 0, "a scanned source window has no minimal reset word");
assert.equal(summary.windowsWithoutSafeActualWitness, 0, "a scanned transition has no safe actual reset witness");
assert.equal(summary.firstResetAtLeftSuffixBad, 0, "left-edge first reset loses nonmonochromaticity after shift");

console.log(JSON.stringify(summary, null, 2));
