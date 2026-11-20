#!/usr/bin/env node
// Independent executable regression check for the sourceDrainSummary/runStats
// bridge proof sketch. This is a computational check, not a proof.

const transitions = {
  A: [[2n, "B"], [1n, "A"], [0n, "C"]],
  B: [[0n, "A"], [2n, "B"], [1n, "A"]],
  C: [[1n, "A"], [0n, "C"], [2n, "A"]],
};

function sourceDrainStep(k) {
  const r = k % 3n;
  if (r === 1n) {
    const [v, q, eps] = sourceDrainStep(k / 3n);
    return [v + 1n, q, eps];
  }
  return [0n, k / 3n, r / 2n];
}

function sourceDrainSummary(b) {
  if (b === 0n) return [0n, 0n, 0n];
  const [v, q, eps] = sourceDrainStep(b - 1n);
  const [L, E, R] = sourceDrainSummary(q);
  return [v + 1n + L, eps + E, 1n + R];
}

function runStats(n, b, state) {
  let ones = 0n;
  let twos = 0n;
  let output = 0n;
  let place = 1n;
  const word = [];
  for (let i = 0; i < n; i++) {
    const digit = Number(b % 3n);
    b /= 3n;
    const [emitted, nextState] = transitions[state][digit];
    word.push(Number(emitted));
    output += emitted * place;
    place *= 3n;
    if (emitted === 1n) ones++;
    if (emitted === 2n) twos++;
    state = nextState;
  }
  return { ones, twos, output, word, finalState: state };
}

function fail(message, data) {
  process.stderr.write(message + ": " + JSON.stringify(data, (_, v) =>
    typeof v === "bigint" ? v.toString() : v
  ) + "\n");
  process.exit(1);
}

let summaryChecks = 0;
let lengthChecks = 0;
for (let b = 0n; b <= 100000n; b++) {
  const [L, E, R] = sourceDrainSummary(b);
  const stats = runStats(Number(L), b, "A");
  if (stats.twos !== E || stats.ones + stats.twos !== R) {
    fail("source summary / transducer mismatch", { b, L, E, R, stats });
  }
  if (L % 2n !== b % 2n) {
    fail("canonical parity mismatch", { b, L });
  }
  if (b > 0n) {
    const z = 2n * b - 1n;
    if (3n ** (L - 1n) > z || z >= 3n ** (L + 1n)) {
      fail("canonical length-bound mismatch", { b, L, z });
    }
    lengthChecks++;
  }
  if (4n * stats.output !== 2n * b - 1n + 3n ** L) {
    fail("exact output formula mismatch", { b, L, stats });
  }
  summaryChecks++;
}

let offsetChecks = 0;
for (let n = 0; n <= 8; n++) {
  for (let q = 0n; q < 10000n; q++) {
    const bShiftLeft = runStats(n, q + 1n, "B");
    const bShiftRight = runStats(n, q, "A");
    if (JSON.stringify(bShiftLeft.word) !== JSON.stringify(bShiftRight.word)) {
      fail("B-shift output-word mismatch", { n, q, bShiftLeft, bShiftRight });
    }
    const aShiftLeft = runStats(n, q + 1n, "A");
    const aShiftRight = runStats(n, q, "C");
    if (JSON.stringify(aShiftLeft.word) !== JSON.stringify(aShiftRight.word)) {
      fail("A-shift output-word mismatch", { n, q, aShiftLeft, aShiftRight });
    }
    offsetChecks++;
  }
}

const witnessBLeft = runStats(1, 3n, "B");
const witnessBRight = runStats(1, 2n, "A");
const witnessALeft = runStats(1, 3n, "A");
const witnessARight = runStats(1, 2n, "C");
if (JSON.stringify(witnessBLeft.word) !== JSON.stringify(witnessBRight.word) ||
    witnessBLeft.finalState === witnessBRight.finalState ||
    JSON.stringify(witnessALeft.word) !== JSON.stringify(witnessARight.word) ||
    witnessALeft.finalState === witnessARight.finalState) {
  fail("expected output-equal/final-state-different witness failed", {
    witnessBLeft, witnessBRight, witnessALeft, witnessARight
  });
}

process.stdout.write(JSON.stringify({
  sourceSummaryChecks,
  lengthChecks,
  offsetChecksPerIdentity: offsetChecks,
  outputWordMismatches: 0,
  finalStateCaveatWitnesses: {
    BShift: { left: witnessBLeft, right: witnessBRight },
    AShift: { left: witnessALeft, right: witnessARight }
  }
}, (_, v) => typeof v === "bigint" ? v.toString() : v, 2) + "\n");
