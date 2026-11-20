#!/usr/bin/env node
"use strict";

// Exact finite-state enumeration of minimal common reset words for the
// #623 signed-coordinate L/R digit-pair transducers. No root replay is done.
// A pattern resets both branch transducers from every full-range start state
// and forces each trajectory's x-output to contain a digit != 0 and != 2.
//
// Usage:
//   node reset_patterns.js
//   node reset_patterns.js --emit-patterns
//   node reset_patterns.js --verify-stdin < root-word-blocks.txt
//
// Input to --verify-stdin is the line format emitted by
// synchronizing_word_scan.js --emit-blocks:
//   index length xy xy xy ...

const readline = require("node:readline");

function buildTransducer(branch) {
  const amin = branch === "L" ? -2 : -4;
  const amax = branch === "L" ? 2 : 1;
  const aCount = amax - amin + 1;
  const stateCount = 9 * aCount * 5;
  const next = new Int16Array(stateCount * 9);
  const outFlags = new Uint8Array(stateCount * 9);
  next.fill(-1);

  for (let xp = 0; xp < 3; xp++) {
    for (let yp = 0; yp < 3; yp++) {
      for (let a = amin; a <= amax; a++) {
        for (let b = -2; b <= 2; b++) {
          const state = (((xp * 3 + yp) * aCount + (a - amin)) * 5 + (b + 2));
          for (let x = 0; x < 3; x++) {
            for (let y = 0; y < 3; y++) {
              let tx, ty;
              if (branch === "L") {
                tx = x - yp + a;
                ty = yp + b;
              } else {
                tx = -x - xp - yp + a;
                ty = xp + yp + b;
              }
              const ox = ((tx % 3) + 3) % 3;
              const an = Math.floor(tx / 3);
              const bn = Math.floor(ty / 3);
              // The full rectangles are invariant; retain this check so the
              // generator fails closed if the transducer definition changes.
              if (an < amin || an > amax || bn < -2 || bn > 2) continue;
              const target =
                (((x * 3 + y) * aCount + (an - amin)) * 5 + (bn + 2));
              const index = state * 9 + x * 3 + y;
              next[index] = target;
              outFlags[index] = (ox !== 0 ? 1 : 0) | (ox !== 2 ? 2 : 0);
            }
          }
        }
      }
    }
  }
  return { branch, next, outFlags, stateCount };
}

const L = buildTransducer("L");
const R = buildTransducer("R");
const nL = L.stateCount;
const nR = R.stateCount;
const totalStarts = nL + nR;

// The vector state is the exact image of every admissible start state,
// together with the two output flags accumulated on that trajectory.
const stateStack = Array.from({ length: 7 }, () => new Uint16Array(totalStarts));
const flagStack = Array.from({ length: 7 }, () => new Uint8Array(totalStarts));
const initialStates = new Uint16Array(totalStarts);
for (let i = 0; i < totalStarts; i++) initialStates[i] = i < nL ? i : i - nL;

const patternsByLength = {
  3: new Set(),
  4: new Set(),
  5: new Set(),
  6: new Set(),
};

function hasShorterPattern(word) {
  for (let len = 3; len < word.length; len++) {
    const set = patternsByLength[len];
    for (let start = 0; start + len <= word.length; start++) {
      let code = 0;
      for (let j = 0; j < len; j++) code = code * 9 + word[start + j];
      if (set.has(code)) return true;
    }
  }
  return false;
}

function isCommonReset(states, flags) {
  for (let i = 0; i < totalStarts; i++) if (flags[i] !== 3) return false;
  const leftFinal = states[0];
  const rightFinal = states[nL];
  for (let i = 1; i < nL; i++) if (states[i] !== leftFinal) return false;
  for (let i = nL + 1; i < totalStarts; i++) {
    if (states[i] !== rightFinal) return false;
  }
  return true;
}

let visitedPrefixes = 0;
let invalidPrefixes = 0;

function enumerate(depth, states, flags, word, code) {
  visitedPrefixes++;
  // Keep only substring-minimal patterns. Any extension of a word already
  // containing a common reset pattern is redundant for recognition.
  if (depth >= 3 && hasShorterPattern(word)) return;
  if (depth >= 3 && isCommonReset(states, flags)) {
    patternsByLength[depth].add(code);
    return;
  }
  if (depth === 6) return;

  const nextStates = stateStack[depth + 1];
  const nextFlags = flagStack[depth + 1];
  for (let symbol = 0; symbol < 9; symbol++) {
    let valid = true;
    for (let i = 0; i < totalStarts; i++) {
      const transducer = i < nL ? L : R;
      const target = transducer.next[states[i] * 9 + symbol];
      if (target < 0) {
        valid = false;
        break;
      }
      nextStates[i] = target;
      nextFlags[i] = flags[i] | transducer.outFlags[states[i] * 9 + symbol];
    }
    if (!valid) {
      invalidPrefixes++;
      continue;
    }
    word.push(symbol);
    enumerate(depth + 1, nextStates, nextFlags, word, code * 9 + symbol);
    word.pop();
  }
}

enumerate(0, initialStates, new Uint8Array(totalStarts), [], 0);

function decodePattern(code, length) {
  const digits = new Array(length);
  for (let i = length - 1; i >= 0; i--) {
    digits[i] = code % 9;
    code = Math.floor(code / 9);
  }
  return digits;
}

// Build an Aho-Corasick DFA for the finite reset-pattern language.
function buildResetDFA() {
  const children = [new Int32Array(9)];
  children[0].fill(-1);
  const fail = [0];
  const terminalLength = [0];
  let nodeCount = 1;

  for (let length = 3; length <= 6; length++) {
    for (const code of patternsByLength[length]) {
      const digits = decodePattern(code, length);
      let state = 0;
      for (const symbol of digits) {
        let target = children[state][symbol];
        if (target < 0) {
          target = nodeCount++;
          children[state][symbol] = target;
          const row = new Int32Array(9);
          row.fill(-1);
          children.push(row);
          fail.push(0);
          terminalLength.push(0);
        }
        state = target;
      }
      terminalLength[state] = length;
    }
  }

  const go = children;
  const outMinLength = new Uint8Array(nodeCount);
  const queue = [];
  for (let symbol = 0; symbol < 9; symbol++) {
    const target = go[0][symbol];
    if (target >= 0) {
      fail[target] = 0;
      outMinLength[target] = terminalLength[target];
      queue.push(target);
    } else {
      go[0][symbol] = 0;
    }
  }

  for (let head = 0; head < queue.length; head++) {
    const state = queue[head];
    for (let symbol = 0; symbol < 9; symbol++) {
      const target = go[state][symbol];
      if (target >= 0) {
        const fallback = go[fail[state]][symbol];
        fail[target] = fallback;
        const own = terminalLength[target];
        const inherited = outMinLength[fallback];
        outMinLength[target] =
          own && inherited ? Math.min(own, inherited) : (own || inherited);
        queue.push(target);
      } else {
        go[state][symbol] = go[fail[state]][symbol];
      }
    }
  }

  return { go, outMinLength, nodeCount };
}

const patternCounts = {};
let patternCount = 0;
for (let length = 3; length <= 6; length++) {
  patternCounts[length] = patternsByLength[length].size;
  patternCount += patternCounts[length];
}
const dfa = buildResetDFA();

function minimizeResetDFA(aho) {
  const sink = aho.nodeCount;
  const count = aho.nodeCount + 1;
  const trans = Array.from({ length: count }, () => new Uint32Array(9));
  const accepting = new Uint8Array(count);
  accepting[sink] = 1;

  for (let state = 0; state < aho.nodeCount; state++) {
    accepting[state] = aho.outMinLength[state] ? 1 : 0;
    for (let symbol = 0; symbol < 9; symbol++) {
      const target = aho.go[state][symbol];
      trans[state][symbol] =
        accepting[state] || aho.outMinLength[target] ? sink : target;
    }
  }
  trans[sink].fill(sink);

  // Moore partition refinement: accepting/nonaccepting initially, then
  // refine by the nine successor classes until the partition is stable.
  let classes = new Uint32Array(count);
  for (let state = 0; state < count; state++) {
    classes[state] = accepting[state] ? 1 : 0;
  }
  const partitionCounts = [];
  let previousCount = -1;
  for (let iteration = 0; iteration < 32; iteration++) {
    const signatures = new Map();
    const nextClasses = new Uint32Array(count);
    let nextCount = 0;
    for (let state = 0; state < count; state++) {
      const signature =
        classes[state] + "," +
        Array.from(trans[state], (target) => classes[target]).join(",");
      let id = signatures.get(signature);
      if (id === undefined) {
        id = nextCount++;
        signatures.set(signature, id);
      }
      nextClasses[state] = id;
    }
    classes = nextClasses;
    partitionCounts.push(nextCount);
    if (nextCount === previousCount) break;
    previousCount = nextCount;
  }

  const classCount = partitionCounts[partitionCounts.length - 1];
  const representatives = new Int32Array(classCount);
  representatives.fill(-1);
  for (let state = 0; state < count; state++) {
    if (representatives[classes[state]] < 0) {
      representatives[classes[state]] = state;
    }
  }
  const minimizedTransitions = Array.from({ length: classCount }, (_, id) => {
    const representative = representatives[id];
    return Array.from(trans[representative], (target) => classes[target]);
  });
  const minimizedAccepting = Array.from(
    representatives,
    (representative) => accepting[representative] === 1,
  );
  return {
    stateCount: classCount,
    initialState: classes[0],
    accepting: minimizedAccepting,
    transitions: minimizedTransitions,
    partitionCounts,
  };
}

const minimizedDFA = minimizeResetDFA(dfa);

const summary = {
  startStates: { L: nL, R: nR, total: totalStarts },
  minimalCommonResetPatterns: patternCounts,
  totalMinimalPatterns: patternCount,
  ahoCorasickStates: dfa.nodeCount,
  minimalDFAStates: minimizedDFA.stateCount,
  minimizationPartitionCounts: minimizedDFA.partitionCounts,
  visitedPrefixes,
  invalidPrefixes,
};

if (process.argv.includes("--emit-minimized-dfa")) {
  process.stdout.write(JSON.stringify({
    alphabet: "digit pairs encoded as 3*x+y",
    initialState: minimizedDFA.initialState,
    accepting: minimizedDFA.accepting,
    transitions: minimizedDFA.transitions,
  }) + "\\n");
}

if (process.argv.includes("--emit-patterns")) {
  for (let length = 3; length <= 6; length++) {
    for (const code of patternsByLength[length]) {
      const word = decodePattern(code, length)
        .map((z) => `${Math.floor(z / 3)}${z % 3}`)
        .join(" ");
      process.stdout.write(`${length} ${word}\n`);
    }
  }
}

if (process.argv.includes("--verify-stdin")) {
  const rl = readline.createInterface({ input: process.stdin, crlfDelay: Infinity });
  const minLengthCounts = new Map();
  const earliestEndCounts = new Map();
  let totalWords = 0;
  rl.on("line", (line) => {
    const fields = line.trim().split(/\s+/);
    if (fields.length < 2) return;
    const index = fields[0];
    const length = Number(fields[1]);
    if (!Number.isInteger(length) || fields.length < length + 2) return;
    let state = 0;
    let bestLength = 99;
    let earliestEnd = 999;
    for (let i = 0; i < length; i++) {
      const pair = fields[i + 2];
      const x = Number(pair[0]);
      const y = Number(pair[1]);
      if (x < 0 || x > 2 || y < 0 || y > 2) continue;
      state = dfa.go[state][x * 3 + y];
      if (dfa.outMinLength[state]) {
        bestLength = Math.min(bestLength, dfa.outMinLength[state]);
        earliestEnd = Math.min(earliestEnd, i + 1);
      }
    }
    minLengthCounts.set(bestLength, (minLengthCounts.get(bestLength) || 0) + 1);
    earliestEndCounts.set(earliestEnd, (earliestEndCounts.get(earliestEnd) || 0) + 1);
    totalWords++;
    process.stdout.write(`word ${index} resetLength ${bestLength} earliestEnd ${earliestEnd}\n`);
  });
  rl.on("close", () => {
    const sortEntries = (m) => [...m.entries()].sort((a, b) => a[0] - b[0]);
    process.stdout.write(JSON.stringify({
      ...summary,
      verifiedWords: totalWords,
      minimumResetLengthDistribution: sortEntries(minLengthCounts),
      earliestResetEndDistribution: sortEntries(earliestEndCounts),
    }, null, 2) + "\n");
  });
} else {
  process.stdout.write(JSON.stringify(summary, null, 2) + "\n");
}
