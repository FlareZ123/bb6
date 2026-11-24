#!/usr/bin/env node
"use strict";

// Reproduce six S4 suffix-renormalization levels and the deeper 15-digit return.
// Q's 18-prefix scan uses Number only under the explicit mass bound (< 2^53);
// every later level, full-stack gate, and accumulated sum uses BigInt.

function assert(ok, message) {
  if (!ok) throw new Error(message);
}
function same(a, b) {
  return a.length === b.length && a.every((x, i) => x === b[i]);
}
function show(xs) { return xs.map(String); }
function sumWord(word) { return word.reduce((s, x) => s + x, 0n); }
function weightedW(xs) {
  let w = 0n;
  for (let i = xs.length - 1; i >= 0; i--) w = xs[i] + 1n + 2n * w;
  return w;
}

function boundary(p, c) {
  let a = p[0] + c;
  for (let i = 0; i < p.length; i++) {
    if ((a & 1n) === 0n)
      return i === p.length - 1
        ? { kind: 1, d: a / 2n }
        : { kind: 0, d: 0n };
    if (i === p.length - 1) return { kind: 2, d: a / 2n + 1n };
    a = p[i + 1] + a / 2n + 1n;
  }
  return { kind: 0, d: 0n };
}

function prefixStep(p, c) {
  p = p.slice();
  let a = p[0] + c;
  for (let i = 0; i < p.length; i++) {
    if (i === p.length - 1) {
      p[i] = a / 2n + ((a & 1n) === 1n ? 0n : 2n);
      return p;
    }
    if ((a & 1n) === 0n) {
      const h = a / 2n;
      p[i] = h + 2n;
      p[i + 1] += h;
      return p;
    }
    const h = a / 2n;
    p[i] = h;
    a = p[i + 1] + h + 1n;
  }
  return p;
}

let trackFullSuffixEvents = false;
let activeYBlock = 0;
let activeYGate = -1;
let activeYBlockMaxDepth = 0;
const yFullSuffixEvents = [];

function gate(c, xs) {
  const out = [];
  let a = xs.length === 0 ? c - 1n : xs[0] + c;
  let i = xs.length === 0 ? 0 : 1;

  while (i < xs.length && (a & 1n) === 1n) {
    out.push(a / 2n);
    a = xs[i] + a / 2n + 1n;
    i++;
  }

  if (trackFullSuffixEvents) {
    if (i > activeYBlockMaxDepth) activeYBlockMaxDepth = i;
    if (i === xs.length) {
      const numerator = weightedW(xs) + c;
      const denominator = 1n << BigInt(Math.max(0, xs.length - 1));
      assert(numerator % denominator === 0n,
        "full-suffix carry did not give an integral terminal quotient");
      const quotient = numerator / denominator;
      let oddPart = quotient;
      while (oddPart > 0n && oddPart % 2n === 0n) oddPart /= 2n;
      let quotientV3 = 0;
      let quotientOddPart = quotient;
      while (quotientOddPart > 0n && quotientOddPart % 3n === 0n) {
        quotientOddPart /= 3n;
        quotientV3++;
      }
      yFullSuffixEvents.push({
        block: activeYBlock,
        gate: activeYGate,
        offset: String(c),
        offsetMod3: String(c % 3n),
        length: xs.length,
        inputTail: show(xs),
        inputWeightedMass: String(weightedW(xs)),
        inputWeightedMassMod3: String(weightedW(xs) % 3n),
        numeratorMod3: String(numerator % 3n),
        numeratorMod9: String(numerator % 9n),
        quotient: String(quotient),
        quotientMod3: String(quotient % 3n),
        quotientMod9: String(quotient % 9n),
        quotientV3,
        oddPart: String(oddPart),
        halts: oddPart === 1n
      });
    }
  }

  if ((a & 1n) === 1n) {
    while ((a & 1n) === 1n) {
      if (a <= 1n) return null;
      out.push(a / 2n);
      a /= 2n;
    }
    if (a === 0n) return null;
    out.push(a / 2n + 2n, a / 2n - 1n);
  } else if (i < xs.length) {
    out.push(a / 2n + 2n, xs[i] + a / 2n);
    for (++i; i < xs.length; i++) out.push(xs[i]);
  } else {
    if (a === 0n) return null;
    out.push(a / 2n + 2n, a / 2n - 1n);
  }
  return out;
}

function applyWord(word, xs) {
  let state = xs;
  let index = 0;
  for (const c of word) {
    if (trackFullSuffixEvents) activeYGate = index;
    index++;
    state = gate(c, state);
    if (state === null) return null;
  }
  return state;
}

function prefixRun(word, prefix, blocks) {
  let state = prefix;
  for (let k = 0; k < blocks; k++)
    for (const c of word) state = prefixStep(state, c);
  return state;
}

function findCycle(word, initial, limit) {
  let state = initial.slice();
  const seen = new Map();
  for (let k = 0; k <= limit; k++) {
    const key = state.map(String).join(",");
    if (seen.has(key))
      return { preperiod: seen.get(key), period: k - seen.get(key) };
    seen.set(key, k);
    for (const c of word) state = prefixStep(state, c);
  }
  throw new Error("cycle not found within " + limit + " blocks");
}

function extractWord(prefixStart, baseWord, blocks, name) {
  let prefix = prefixStart.slice();
  let pending = 0n;
  let adds = 0;
  const word = [];

  for (let k = 0; k < blocks; k++) {
    for (const c of baseWord) {
      const e = boundary(prefix, c);
      if (e.kind === 1) {
        pending += e.d;
        adds++;
      } else if (e.kind === 2) {
        word.push(e.d + pending);
        pending = 0n;
      }
      prefix = prefixStep(prefix, c);
    }
  }

  assert(pending === 0n, name + ": nonzero pending carry");
  assert(same(prefix, prefixStart), name + ": prefix did not return");
  return { word, adds };
}

function checkMass(name, word, returns) {
  const total = sumWord(word) + 2n * BigInt(word.length);
  const expected = 1024n * returns;
  assert(total === expected, name + ": mass identity failed");
  return { returns: String(returns), offsetSum: String(sumWord(word)),
    gates: word.length, headAdds: null, massIdentity: true };
}

// Q: the 18-digit prefix cycle, 64 blocks of 327,680 P-returns.
// Its coordinates are bounded by total prefix mass < 2^53, so Number
// arithmetic is exact here; all extracted offsets are immediately BigInt'd.
const OFF_N = [509, 290, 219];
function boundaryN(p, c) {
  let a = p[0] + c;
  for (let i = 0; i < p.length; i++) {
    if (a % 2 === 0)
      return i === p.length - 1
        ? { kind: 1, d: a / 2 }
        : { kind: 0, d: 0 };
    if (i === p.length - 1) return { kind: 2, d: Math.floor(a / 2) + 1 };
    a = p[i + 1] + Math.floor(a / 2) + 1;
  }
  return { kind: 0, d: 0 };
}
function prefixStepN(p, c) {
  p = p.slice();
  let a = p[0] + c;
  for (let i = 0; i < p.length; i++) {
    if (i === p.length - 1) {
      p[i] = Math.floor(a / 2) + (a % 2 === 1 ? 0 : 2);
      return p;
    }
    if (a % 2 === 0) {
      const h = Math.floor(a / 2);
      p[i] = h + 2;
      p[i + 1] += h;
      return p;
    }
    const h = Math.floor(a / 2);
    p[i] = h;
    a = p[i + 1] + h + 1;
  }
  return p;
}

let p18 = [283, 906, 982, 3490, 3734, 5935, 13580, 109210, 171050,
  366446, 435438, 366335, 527037, 2639156, 3037351, 3252483,
  6310511, 24221543];
const p18Start = p18.slice();
const Q = [];
let pendingQ = 0;
let addsQ = 0;

for (let b = 0; b < 64; b++) {
  for (let t = 0; t < 327680; t++) {
    for (const c of OFF_N) {
      const e = boundaryN(p18, c);
      if (e.kind === 1) { pendingQ += e.d; addsQ++; }
      else if (e.kind === 2) {
        Q.push(BigInt(e.d + pendingQ));
        pendingQ = 0;
      }
      p18 = prefixStepN(p18, c);
    }
  }
  const prefixMass = p18.reduce((s, x) => s + x + 1, 0);
  assert(Number.isSafeInteger(prefixMass) && prefixMass < Number.MAX_SAFE_INTEGER,
    "Q prefix mass exceeded exact Number range");
}
assert(same(p18, p18Start) && pendingQ === 0 && Q.length === 386,
  "Q extraction failed");
const qMass = checkMass("Q", Q, 64n * 327680n);
qMass.headAdds = addsQ;

// The full-stack state at the first-level macro root (block 68).
const blockRootTail = [24423525n, 56750562n, 67602890n, 162126013n,
  335820941n, 659578070n];
let tail18 = blockRootTail.slice();
for (let k = 0; k < 107; k++) {
  tail18 = applyWord(Q, tail18);
  assert(tail18 !== null, "halt in 107-block Q transient");
}
const rStar = [22012582n, 64906605n, 290229088n, 678591099n,
  1868575904n, 5618853814n, 6383903289n, 7119998521n,
  5023439474n, 18625025781n];
assert(same(tail18.slice(0, 10), rStar), "r* mismatch");
const tailAfter28 = tail18.slice(10);

// R: 10-digit prefix cycle, 12,800 Q-blocks.
const Rdata = extractWord(rStar, Q, 12800, "R");
const R = Rdata.word;
const rMass = checkMass("R", R, 12800n * 64n * 327680n);
rMass.headAdds = Rdata.adds;
let tail35 = applyWord(R, tailAfter28);
assert(tail35 !== null, "halt in one R block");
const sStar = [146121173630n, 123211293236n, 150769158159n,
  655928122993n, 1188500987335n, 5911406347889n, 4869186526586n];
assert(same(tail35.slice(0, 7), sStar), "s* mismatch");
const tailAfter35 = tail35.slice(7);

// V: 7-digit prefix cycle, 800 R-blocks.
const Vdata = extractWord(sStar, R, 800, "V");
const V = Vdata.word;
const vMass = checkMass("V", V, 800n * 12800n * 64n * 327680n);
vMass.headAdds = Vdata.adds;
const tailAfterV = applyWord(V, tailAfter35);
assert(tailAfterV !== null, "halt in one V block");
const p8BeforeV = tailAfter35.slice(0, 8);
const p8AfterV = tailAfterV.slice(0, 8);
const vCycle = findCycle(V, p8BeforeV, 100);
assert(vCycle.preperiod === 1 && vCycle.period === 64, "V eight-prefix cycle");
assert(same(prefixRun(V, p8AfterV, 64), p8AfterV), "V period check");

// W: 8-digit prefix cycle, 64 V-blocks.
const Wdata = extractWord(p8AfterV, V, 64, "W");
const W = Wdata.word;
const wMass = checkMass("W", W, 64n * 800n * 12800n * 64n * 327680n);
wMass.headAdds = Wdata.adds;
const tailAfterW = applyWord(W, tailAfterV.slice(8));
assert(tailAfterW !== null, "halt in one W block");
const p7BeforeW = tailAfterV.slice(8, 15);
const p7AfterW = tailAfterW.slice(0, 7);
const wCycle = findCycle(W, p7BeforeW, 1000);
assert(wCycle.preperiod === 1 && wCycle.period === 640, "W seven-prefix cycle");

// X: 7-digit prefix cycle, 640 W-blocks.
const Xdata = extractWord(p7AfterW, W, 640, "X");
const X = Xdata.word;
const xMass = checkMass("X", X, 640n * 64n * 800n * 12800n * 64n * 327680n);
xMass.headAdds = Xdata.adds;
const tailAfterX = applyWord(X, tailAfterW.slice(7));
assert(tailAfterX !== null, "halt in one X block");
const p8BeforeX = tailAfterW.slice(7, 15);
const p8AfterX = tailAfterX.slice(0, 8);
const xCycle = findCycle(X, p8BeforeX, 300);
assert(xCycle.preperiod === 1 && xCycle.period === 128, "X eight-prefix cycle");

// Y: 8-digit prefix cycle, 128 X-blocks.
const Ydata = extractWord(p8AfterX, X, 128, "Y");
const Y = Ydata.word;
const yMass = checkMass("Y", Y, 128n * 640n * 64n * 800n * 12800n * 64n * 327680n);
yMass.headAdds = Ydata.adds;
const tailAfterY = applyWord(Y, tailAfterX.slice(8));
assert(tailAfterY !== null, "halt in one Y block");

function extractWordWithPending(prefixStart, baseWord, blocks, name) {
  let prefix = prefixStart.slice();
  let pending = 0n;
  let adds = 0;
  const word = [];
  for (let k = 0; k < blocks; k++) {
    for (const c of baseWord) {
      const e = boundary(prefix, c);
      if (e.kind === 1) { pending += e.d; adds++; }
      else if (e.kind === 2) { word.push(e.d + pending); pending = 0n; }
      prefix = prefixStep(prefix, c);
    }
  }
  assert(same(prefix, prefixStart), name + ": prefix did not return");
  return { word, pending, adds, finalPrefix: prefix };
}
function extractSkewedWord(prefixStart, baseWord, basePending, blocks, name) {
  let prefix = prefixStart.slice();
  let pending = 0n;
  let adds = 0;
  const word = [];
  for (let k = 0; k < blocks; k++) {
    for (const c of baseWord) {
      const e = boundary(prefix, c);
      if (e.kind === 1) { pending += e.d; adds++; }
      else if (e.kind === 2) { word.push(e.d + pending); pending = 0n; }
      prefix = prefixStep(prefix, c);
    }
    // The base map's skew is a head addition inside this tracked prefix.
    prefix[0] = prefix[0] + basePending;
  }
  assert(same(prefix, prefixStart), name + ': prefix did not return');
  return { word, pending, adds, finalPrefix: prefix };
}

function findSkewedPrefixCycle(word, pending, initial, limit) {
  let state = initial.slice();
  const seen = new Map();
  for (let k = 0; k <= limit; k++) {
    const key = state.map(String).join(',');
    if (seen.has(key)) return { preperiod: seen.get(key), period: k - seen.get(key) };
    seen.set(key, k);
    state = prefixSkewedWord(word, pending, state);
  }
  return null;
}
function scanCycleCarry(word, pending, initial, cycle, digits) {
  let prefix = initial.slice();
  let maxDepth = 0;
  let maxWitness = null;
  let boundaryEvents = 0;
  const coveredBlocks = cycle.preperiod + cycle.period;
  for (let phase = 0; phase < coveredBlocks; phase++) {
    for (let gateIndex = 0; gateIndex < word.length; gateIndex++) {
      const depth = prefixCarryDepth(prefix, word[gateIndex]);
      if (depth > maxDepth) {
        maxDepth = depth;
        maxWitness = { phase, gate: gateIndex, depth, offset: String(word[gateIndex]) };
      }
      if (depth === digits) boundaryEvents++;
      prefix = prefixStep(prefix, word[gateIndex]);
    }
    prefix[0] = prefix[0] + pending;
  }
  return { maxDepth, maxWitness, boundaryEvents, coveredBlocks, barrier: maxDepth < digits };
}
function shiftedWord(word, delta) {
  const out = word.slice();
  out[0] += delta;
  return out;
}
function repeatSkewedWord(word, pending, blocks) {
  const out = [];
  for (let k = 0; k < blocks; k++) {
    const part = k === 0 ? word : shiftedWord(word, pending);
    for (const c of part) out.push(c);
  }
  return out;
}
function applySkewedWord(word, pending, xs) {
  const out = applyWord(word, xs.slice());
  if (out === null) return null;
  out[0] += pending;
  return out;
}
function prefixSkewedWord(word, pending, prefix) {
  let out = prefix.slice();
  for (const c of word) out = prefixStep(out, c);
  out[0] += pending;
  return out;
}
function verifyNestedFactor(name, baseWord, basePending, blocks,
    prefix, suffix, extractedWord, extractedPending) {
  let direct = [...prefix, ...suffix];
  for (let k = 0; k < blocks; k++) {
    direct = applyWord(baseWord, direct);
    assert(direct !== null, name + ": direct composition halted");
    direct[0] += basePending;
  }
  const mapped = applySkewedWord(extractedWord, extractedPending, suffix);
  assert(mapped !== null, name + ": extracted suffix map halted");
  assert(same(direct, [...prefix, ...mapped]),
    name + ": all-suffix factorization witness mismatch");
  return { name, verified: true, blocks, resultingLength: direct.length };
}
function checkSkewedPrefixCycle(name, word, pending, initial, period) {
  let state = initial.slice();
  const firstDigits = [String(state[0])];
  for (let k = 1; k <= period; k++) {
    state = prefixSkewedWord(word, pending, state);
    firstDigits.push(String(state[0]));
    if (k < period)
      assert(!same(state, initial), name + ": period was not minimal");
  }
  assert(same(state, initial), name + ": prefix did not return");
  return { name, period, firstDigits };
}
function scanSkewedPrefixPeriods(word, pending, initial, maxBlocks, maxDigits) {
  let state = initial.slice();
  const seen = Array.from({ length: maxDigits + 1 }, () => new Map());
  const periods = Array(maxDigits + 1).fill(null);
  for (let n = 1; n <= maxDigits; n++)
    seen[n].set(state.slice(0, n).map(String).join(","), 0);
  const lengthChanges = [];
  let previousLength = state.length;
  for (let block = 1; block <= maxBlocks; block++) {
    state = applySkewedWord(word, pending, state);
    assert(state !== null, "skewed prefix scan halted at block " + block);
    if (state.length !== previousLength) {
      lengthChanges.push({ block, from: previousLength, to: state.length });
      previousLength = state.length;
    }
    for (let n = 1; n <= maxDigits; n++) {
      if (periods[n] !== null) continue;
      const key = state.slice(0, n).map(String).join(",");
      if (seen[n].has(key)) {
        const first = seen[n].get(key);
        periods[n] = { preperiod: first, period: block - first, returnAt: block };
      } else seen[n].set(key, block);
    }
  }
  return {
    blocks: maxBlocks,
    maxDigits,
    periods: periods.slice(1),
    lengthChanges,
    initialLength: initial.length,
    finalLength: state.length,
    initialPrefix: show(initial.slice(0, maxDigits)),
    finalPrefix: show(state.slice(0, maxDigits))
  };
}
function checkMassWithPending(name, word, pending, returns, headAdds) {
  const offsetSum = sumWord(word);
  const total = offsetSum + 2n * BigInt(word.length) + pending;
  const expected = 1024n * returns;
  assert(total === expected, name + ": pending-aware mass identity failed");
  return {
    returns: String(returns),
    gates: word.length,
    headAdds,
    pending: String(pending),
    offsetSum: String(offsetSum),
    massTotal: String(total),
    massIdentity: true
  };
}

// Y's first suffix digit (the ninth root digit) has period five.
// Extract Z = Y^5 on the suffix after that digit.
const yReturns = 128n * 640n * 64n * 800n * 12800n * 64n * 327680n;
const Zdata = extractWordWithPending(tailAfterY.slice(0, 1), Y, 5, "Z");
const Z = Zdata.word;
assert(Zdata.pending === 0n, "Z unexpectedly has a pending head addition");
const tailAfterZ = applyWord(Z, tailAfterY.slice(1));
assert(tailAfterZ !== null, "halt in one Z block");

// Four Z blocks return the tenth digit and induce a skewed map F on the
// suffix after it: F(S) = addHead(pF, applyWord(Fword, S)).
const Fdata = extractWordWithPending(tailAfterZ.slice(0, 1), Z, 4, "F");
const Fword = Fdata.word;
const pF = Fdata.pending;
const F1Tail = applySkewedWord(Fword, pF, tailAfterZ.slice(1));
assert(F1Tail !== null, "halt in one F block");

// Verify the two nested all-suffix factorizations on the actual suffixes.
const nestedFactorChecks = [
  verifyNestedFactor("Y^5 -> Z", Y, 0n, 5,
    tailAfterY.slice(0, 1), tailAfterY.slice(1), Z, Zdata.pending),
  verifyNestedFactor("Z^4 -> F", Z, 0n, 4,
    tailAfterZ.slice(0, 1), tailAfterZ.slice(1), Fword, pF)
];

// The first digit of each successive suffix has a small exact cycle.
const nestedCycles = [
  checkSkewedPrefixCycle("ninth digit under Y", Y, 0n,
    tailAfterY.slice(0, 1), 5),
  checkSkewedPrefixCycle("tenth digit under Z", Z, 0n,
    tailAfterZ.slice(0, 1), 4),
  checkSkewedPrefixCycle("eleventh digit under F", Fword, pF,
    tailAfterZ.slice(1, 2), 4)
];

// Starting after one F block, the first five digits of the remaining suffix
// have exact periods 4, 16, 64, 320, 1280. The scan applies the full skewed
// word to the full suffix, not merely to a truncated prefix.
const F_PREFIX_SCAN_BLOCKS = 1280;
const F_PREFIX_SCAN_DIGITS = 5;
const FprefixPeriodScan = scanSkewedPrefixPeriods(
  Fword, pF, F1Tail, F_PREFIX_SCAN_BLOCKS, F_PREFIX_SCAN_DIGITS);
const expectedFPeriods = [4, 16, 64, 320, 1280];
for (let i = 0; i < expectedFPeriods.length; i++) {
  const found = FprefixPeriodScan.periods[i];
  assert(found !== null && found.preperiod === 0 &&
    found.period === expectedFPeriods[i],
    "F prefix period mismatch at depth " + (i + 1));
}

// One F block is Z^4 = Y^20. The 15-digit root prefix therefore reaches
// this eventual cycle after 25 additional Y blocks and returns after 25,600.
const first15CycleStart = [
  ...p8AfterX, tailAfterY[0], tailAfterZ[0], ...F1Tail.slice(0, 5)
];
assert(first15CycleStart.length === 15, "15-digit cycle prefix length");
const first15PreperiodYBlocks = 25n;
const first15PeriodYBlocks = 20n * BigInt(FprefixPeriodScan.periods[4].period);
const first15Cycle = {
  cycleStartAfterAdditionalYBlocks: String(first15PreperiodYBlocks),
  oneBasedYBlockAtCycleStart: String(first15PreperiodYBlocks + 1n),
  witnessedPeriodYBlocks: String(first15PeriodYBlocks),
  yReturnsPerBlock: String(yReturns),
  preperiodPReturns: String(first15PreperiodYBlocks * yReturns),
  periodPReturns: String(first15PeriodYBlocks * yReturns),
  first15DigitsAtCycleStart: show(first15CycleStart)
};
// G is the induced suffix word after 1,280 skewed F blocks. The outer ten
// digits are fixed by the Z/F hierarchy; F's own five-digit prefix returns.
// This replaces a brute-force 25,600-Y-block search with a boundary-word test.
const tailAfter15 = F1Tail.slice(5);
assert(tailAfter15.length >= 15, 'G requires at least 15 residual digits');
const Gdata = extractSkewedWord(F1Tail.slice(0, 5), Fword, pF, 1280, 'G');
const G = Gdata.word;
const gMass = checkMassWithPending('G', G, Gdata.pending, 1280n * 20n * yReturns, Gdata.adds);
const gPrefixStart = tailAfter15.slice(0, 15);
function prefixCyclesWithCarry(word, pending, initial, maxDigits, limit) {
  const seen = Array.from({ length: maxDigits + 1 }, () => new Map());
  const cycles = Array(maxDigits + 1).fill(null);
  let state = initial.slice();
  const blockCarry = [];
  for (let k = 0; k <= limit; k++) {
    for (let d = 1; d <= maxDigits; d++) {
      if (cycles[d] !== null) continue;
      const key = state.slice(0, d).map(String).join(',');
      if (seen[d].has(key)) {
        const previous = seen[d].get(key);
        cycles[d] = { preperiod: previous, period: k - previous };
      } else {
        seen[d].set(key, k);
      }
    }
    if (k === limit) break;
    let maxDepth = 0;
    let maxWitness = null;
    for (let gateIndex = 0; gateIndex < word.length; gateIndex++) {
      const depth = prefixCarryDepth(state, word[gateIndex]);
      if (depth > maxDepth) {
        maxDepth = depth;
        maxWitness = { block: k, gate: gateIndex, depth, offset: String(word[gateIndex]) };
      }
      state = prefixStep(state, word[gateIndex]);
    }
    state[0] += pending;
    blockCarry.push({ maxDepth, maxWitness });
  }
  return { cycles, blockCarry };
}
function carrySummariesForCycles(scan, maxDigits) {
  const cycles = {};
  const carry = {};
  for (let d = 1; d <= maxDigits; d++) {
    const cycle = scan.cycles[d];
    if (cycle === null) continue;
    cycles[d] = cycle;
    const coveredBlocks = cycle.preperiod + cycle.period;
    let maxDepth = 0;
    let maxWitness = null;
    for (let phase = 0; phase < coveredBlocks; phase++) {
      const record = scan.blockCarry[phase];
      const depth = Math.min(record.maxDepth, d);
      if (depth > maxDepth) {
        maxDepth = depth;
        maxWitness = record.maxWitness;
      }
    }
    carry[d] = { maxDepth, maxWitness, coveredBlocks, barrier: maxDepth < d };
  }
  return { cycles, carry };
}

const G_PREFIX_CYCLE_LIMIT = 16;
const gPrefixScan = prefixCyclesWithCarry(
  G, Gdata.pending, gPrefixStart, 15, G_PREFIX_CYCLE_LIMIT);
const gDepthResults = carrySummariesForCycles(gPrefixScan, 15);
const gPrefixCycle = gPrefixScan.cycles[15];
const gCarrySummary = gDepthResults.carry[15] ?? null;
const gBarrier = gCarrySummary !== null && gCarrySummary.barrier;

// The first digit of the G suffix is a cheaper next section boundary than
// demanding a 15-digit G cycle. Extract its exact return word, then inspect
// the next suffix prefix under that induced word.
const gFirstDigitCycle = gPrefixScan.cycles[1];
let hSummary = null;
if (gFirstDigitCycle !== null) {
  let hRootTail = tailAfter15.slice();
  for (let k = 0; k < gFirstDigitCycle.preperiod; k++) {
    hRootTail = applySkewedWord(G, Gdata.pending, hRootTail);
    assert(hRootTail !== null, "halt in G first-digit transient");
  }
  const hBlocks = gFirstDigitCycle.period;
  const Hdata = extractSkewedWord(
    hRootTail.slice(0, 1), G, Gdata.pending, hBlocks, "H");
  const H = Hdata.word;
  const hReturns = BigInt(hBlocks) * 1280n * 20n * yReturns;
  const hMass = checkMassWithPending(
    "H", H, Hdata.pending, hReturns, Hdata.adds);
  const afterH = applySkewedWord(H, Hdata.pending, hRootTail.slice(1));
  assert(afterH !== null, "halt in one H block");
  const hTrackDigits = Math.min(8, afterH.length);
  const H_PREFIX_CYCLE_LIMIT = 4;
  const hPrefixScan = prefixCyclesWithCarry(
    H, Hdata.pending, afterH.slice(0, hTrackDigits),
    hTrackDigits, H_PREFIX_CYCLE_LIMIT);
  const hDepthResults = carrySummariesForCycles(hPrefixScan, hTrackDigits);
  hSummary = {
    blocks: hBlocks,
    preperiod: gFirstDigitCycle.preperiod,
    word: hMass,
    trackedDigits: hTrackDigits,
    prefixCycleLimit: H_PREFIX_CYCLE_LIMIT,
    prefixCyclesByDepth: hDepthResults.cycles,
    carryByDepth: hDepthResults.carry,
    afterHFirstDigits: show(afterH.slice(0, hTrackDigits))
  };
}
const vCarrySummary = scanCycleCarry(V, 0n, p8BeforeV, vCycle, 8);
const wCarrySummary = scanCycleCarry(W, 0n, p7BeforeW, wCycle, 7);
const xCarrySummary = scanCycleCarry(X, 0n, p8BeforeX, xCycle, 8);
const nestedReturnHierarchy = {
  YtoZ: {
    blocks: 5,
    prefixDigits: 1,
    word: checkMassWithPending("Z", Z, Zdata.pending, 5n * yReturns, Zdata.adds)
  },
  ZtoF: {
    blocks: 4,
    prefixDigits: 1,
    word: checkMassWithPending("F", Fword, pF, 20n * yReturns, Fdata.adds)
  },
  factorizationChecks: nestedFactorChecks,
  prefixCycles: nestedCycles,
  FprefixPeriodScan,
  first15Cycle,
  GtoH: hSummary
};

// Continue the exact BigInt Y-word action for 10,000 additional blocks.
// A full-suffix event is the only place where the terminal quotient is formed;
// its odd part equals 1 exactly when the original source gate halts.
const RUN_LEGACY_Y_SCAN = process.argv.includes('--legacy-y-scan');
const Y_SCAN_ADDITIONAL_BLOCKS = RUN_LEGACY_Y_SCAN ? 10000 : 0;
trackFullSuffixEvents = true;
let yScanState = tailAfterY;
let yScanHaltBlock = null;
let yScanLengthChanges = [];
let yScanDepthRecords = [];
let yScanMaxDepth = 0;
const yBlockPrefixSnapshots = [];
for (let block = 2; block <= Y_SCAN_ADDITIONAL_BLOCKS + 1; block++) {
  activeYBlock = block;
  activeYGate = -1;
  activeYBlockMaxDepth = 0;
  const oldLength = yScanState.length;
  yScanState = applyWord(Y, yScanState);
  if (yScanState !== null && [256, 257, 258, 259, 260, 1000, 10000, 10001].includes(block)) {
    yBlockPrefixSnapshots.push({
      block,
      length: yScanState.length,
      firstFive: show(yScanState.slice(0, 5)),
      lastFive: show(yScanState.slice(-5)),
      weightedMod32: String(weightedW(yScanState) % 32n),
      weightedMod3: String(weightedW(yScanState) % 3n),
      lengthMod3: yScanState.length % 3
    });
  }
  if (activeYBlockMaxDepth > yScanMaxDepth) {
    yScanMaxDepth = activeYBlockMaxDepth;
    yScanDepthRecords.push({ block, maxCarryDepth: yScanMaxDepth });
  }
  if (yScanState === null) {
    yScanHaltBlock = block;
    break;
  }
  if (yScanState.length !== oldLength)
    yScanLengthChanges.push({ block, from: oldLength, to: yScanState.length });
}
trackFullSuffixEvents = false;
const yBlockScan = {
  additionalBlocks: Y_SCAN_ADDITIONAL_BLOCKS,
  totalBlocksFromYStart: yScanHaltBlock ?? (Y_SCAN_ADDITIONAL_BLOCKS + 1),
  haltBlock: yScanHaltBlock,
  lengthChanges: yScanLengthChanges,
  fullSuffixEvents: yFullSuffixEvents,
  maxCarryDepthRecords: yScanDepthRecords,
  finalLength: yScanState === null ? null : yScanState.length,
  finalWeightedMass: yScanState === null ? null : String(weightedW(yScanState)),
  finalLastFiveDigits: yScanState === null ? null : show(yScanState.slice(-5)),
  prefixSnapshots: yBlockPrefixSnapshots,
  finalState: yScanState === null ? null : show(yScanState)
};

// Search for an exact 30-digit Y-prefix cycle after the 10,001-block scan.
// If every gate in the transient+cycle has carry depth < 30, the full suffix
// remains length 30 forever and no future gate can consume it completely.
function findCycleMaybe(word, initial, limit) {
  let state = initial.slice();
  const seen = new Map();
  for (let k = 0; k <= limit; k++) {
    const key = state.map(String).join(",");
    if (seen.has(key))
      return { preperiod: seen.get(key), period: k - seen.get(key) };
    seen.set(key, k);
    for (const c of word) state = prefixStep(state, c);
  }
  return null;
}
function prefixCarryDepth(prefix, c) {
  let a = prefix[0] + c;
  let i = 1;
  while (i < prefix.length && (a & 1n) === 1n) {
    a = prefix[i] + a / 2n + 1n;
    i++;
  }
  return i;
}
const yPrefix30Start = yScanState === null ? null : yScanState.slice(0, 30);
const yPrefix30Cycle = yPrefix30Start === null
  ? null : findCycleMaybe(Y, yPrefix30Start, RUN_LEGACY_Y_SCAN ? 10000 : 0);
let yPrefix30CarrySummary = null;
if (yPrefix30Cycle !== null) {
  let prefix = yPrefix30Start.slice();
  let maxDepth = 0;
  let maxWitness = null;
  let depth30Events = [];
  for (let phase = 0; phase < yPrefix30Cycle.preperiod + yPrefix30Cycle.period; phase++) {
    for (let gateIndex = 0; gateIndex < Y.length; gateIndex++) {
      const depth = prefixCarryDepth(prefix, Y[gateIndex]);
      if (depth > maxDepth) {
        maxDepth = depth;
        maxWitness = { phase, gate: gateIndex, depth, offset: String(Y[gateIndex]) };
      }
      if (depth === 30 && depth30Events.length < 20)
        depth30Events.push({ phase, gate: gateIndex, offset: String(Y[gateIndex]) });
      prefix = prefixStep(prefix, Y[gateIndex]);
    }
  }
  yPrefix30CarrySummary = { maxDepth, maxWitness, depth30EventCountAtLeast: depth30Events.length,
    depth30Events, coveredBlocks: yPrefix30Cycle.preperiod + yPrefix30Cycle.period };
}

// The terminal-quotient experiment requested in the Critic's 14 November note.
// This is a counterexample to the proposed (W mod 31, length mod 5) quotient,
// not a halt on the authentic blank-root orbit.
function weightedMod(xs, m) { return weightedW(xs) % m; }
const terminalRootW = weightedW(tailAfter28);
const terminalRootWmod31 = weightedMod(tailAfter28, 31n);
const terminalFirstOffset = R[0];
assert(terminalFirstOffset === 305419363311n, "unexpected first R offset");
assert(terminalRootW === 57570541714408n && terminalRootWmod31 === 27n,
  "modeled R-section tail changed");
const terminalPowerExponent = 100n;
const terminalPower = 1n << terminalPowerExponent;
const terminalSyntheticW = terminalPower - terminalFirstOffset;
const terminalSyntheticMin = (1n << BigInt(tailAfter28.length)) - 1n;
assert(terminalSyntheticW >= terminalSyntheticMin, "synthetic tail mass too small");
const terminalSyntheticTail = [
  terminalSyntheticW - terminalSyntheticMin,
  ...Array(tailAfter28.length - 1).fill(0n)
];
assert(weightedW(terminalSyntheticTail) === terminalSyntheticW,
  "synthetic tail mass construction failed");
assert(terminalSyntheticTail.length === tailAfter28.length &&
  weightedMod(terminalSyntheticTail, 31n) === terminalRootWmod31,
  "synthetic tail does not share the proposed quotient state");
assert(weightedW(terminalSyntheticTail) + terminalFirstOffset === terminalPower,
  "synthetic terminal power equation failed");
assert(gate(terminalFirstOffset, terminalSyntheticTail) === null,
  "source G did not halt on the constructed power gate");

// The complete R word is not a deterministic map on (W mod 31, length mod 5).
const quotientInputA = [0n, 16n];
const quotientInputB = [1n, 0n];
assert(weightedMod(quotientInputA, 31n) === 4n &&
  weightedMod(quotientInputB, 31n) === 4n &&
  quotientInputA.length % 5 === quotientInputB.length % 5,
  "quotient-collision inputs changed");
const quotientOutputA = applyWord(R, quotientInputA);
const quotientOutputB = applyWord(R, quotientInputB);
assert(quotientOutputA !== null && quotientOutputB !== null,
  "quotient-collision test input unexpectedly halts");
assert(quotientOutputA.length === 12 && quotientOutputB.length === 13 &&
  weightedMod(quotientOutputA, 31n) === 5n &&
  weightedMod(quotientOutputB, 31n) === 5n,
  "R-word quotient non-closure witness changed");
const terminalQuotientObstruction = {
  modeledRootTail: show(tailAfter28),
  modeledRootW: String(terminalRootW),
  modeledRootWmod31: String(terminalRootWmod31),
  modeledRootLength: tailAfter28.length,
  modeledRootLengthMod5: tailAfter28.length % 5,
  firstROffset: String(terminalFirstOffset),
  syntheticHaltingTail: show(terminalSyntheticTail),
  syntheticW: String(terminalSyntheticW),
  syntheticWmod31: String(weightedMod(terminalSyntheticTail, 31n)),
  syntheticLength: terminalSyntheticTail.length,
  powerExponent: String(terminalPowerExponent),
  firstGateHalts: true
};
const quotientNonClosure = {
  inputA: show(quotientInputA),
  inputB: show(quotientInputB),
  commonInputWmod31: "4",
  commonInputLengthMod5: 2,
  outputA: { length: quotientOutputA.length, lengthMod5: quotientOutputA.length % 5,
    Wmod31: String(weightedMod(quotientOutputA, 31n)) },
  outputB: { length: quotientOutputB.length, lengthMod5: quotientOutputB.length % 5,
    Wmod31: String(weightedMod(quotientOutputB, 31n)) }
};

console.log(JSON.stringify({
  levels: {
    Q: qMass, R: rMass, V: vMass, W: wMass, X: xMass, Y: yMass, G: gMass
  },
  prefixCycles: {
    V_eightDigit: vCycle,
    W_sevenDigit: wCycle,
    X_eightDigit: xCycle,
    G_fifteenDigit: gPrefixCycle,
    G_by_depth: gDepthResults.cycles,
    G_carry_by_depth: gDepthResults.carry
  },
  yOffsetMod3Counts: Y.reduce((counts, c) => {
    counts[Number(c % 3n)]++;
    return counts;
  }, [0, 0, 0]),
  yBlockScan,
  yPrefix30Cycle,
  yPrefix30CarrySummary,
  gPrefixCycleLimit: G_PREFIX_CYCLE_LIMIT,
  gCarrySummary,
  gBarrier,
  vCarrySummary,
  wCarrySummary,
  xCarrySummary,
  nestedReturnHierarchy,
  terminalQuotientObstruction,
  quotientNonClosure,
  states: {
    rStar: show(rStar),
    sStar: show(sStar),
    afterV: show(tailAfterV),
    afterW: show(tailAfterW),
    afterX: show(tailAfterX),
    afterY: show(tailAfterY)
  }
}, null, 2));
