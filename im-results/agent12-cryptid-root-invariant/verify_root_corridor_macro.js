// This harness checks #85-side projected stack macros only. It does not
// establish a path from the #490 blank start; use fast_root_stack_sim.js for
// the actual mirrored #490 root trajectory.
#!/usr/bin/env node
"use strict";

// Array-based regression checks for RootCorridorMacro.md and the corrected root countdown/growth path.
// This is an executable transcription of the outer stack/token clauses,
// not a proof. The Lean/source derivations are described in the Markdown note.

const bump = xs => xs.length ? [xs[0] + 1, ...xs.slice(1)] : [1];
const bumpN = (xs, n) => {
  let out = xs.slice();
  for (let i = 0; i < n; i++) out = bump(out);
  return out;
};
const zeros = n => Array(n).fill(0);
const repeat = (xs, n) => Array(n).fill(xs).flat();
const eq = (a, b) => JSON.stringify(a) === JSON.stringify(b);
const state = (mode, L, R) => ({ mode, L, R });

function bounceCR(r, k, a, x) {
  let right = x.slice();
  while (right.length) {
    const v = right[0], t = right.slice(1);
    if (v === 0) { k += 2; right = t; continue; }
    if (v === 1) {
      if (!t.length) return { a: [k + 1, ...a], right: [0, 0, 1] };
      const w = t[0], u = t.slice(1);
      if (w === 0) { a = [k + 4, ...a]; k = 0; right = u; continue; }
      if (w === 1) {
        if (!u.length) return { a: [k + 1, ...a], right: [0, 1] };
        return { a: [k + 1, ...a], right: [0, u[0] + 2, ...u.slice(1)] };
      }
      return bounceDR(r, [1, k + 1, ...a], [w - 2, ...u]);
    }
    return { halt: "tok_CR add2" };
  }
  if (k === 0) return { a, right: [1] };
  if (k === 1) return { a: [0, ...a], right: [0, 1] };
  if (k === 2) return { a: [1, ...a], right: [0, 1] };
  return { a: [k - 1, ...a], right: [0, 1] };
}

function bounceDR(r, a, x) {
  let right = x.slice();
  while (right.length) {
    const v = right[0], t = right.slice(1);
    if (v === 0) { a = [1, ...a]; right = t; continue; }
    if (v === 1 && !t.length) return { a: [1, ...a], right: [0, 0, 1] };
    return bounceCR(r, 0, [1, ...a], [v - 1, ...t]);
  }
  return { a, right: [1] };
}

function normalizeEL(k, r, x) {
  let kk = k.slice(), right = x.slice();
  while (kk.length) {
    const v = kk[0], t = kk.slice(1);
    if (v === 0) {
      if (!t.length) return state("CR", [0, ...right], bump(r));
      const z = bounceCR(r, t[0] + 2, t.slice(1), right);
      if (z.halt) return z;
      kk = z.a; right = z.right; continue;
    }
    if (v === 1) { kk = t; right = [0, ...right]; continue; }
    if (v === 2) { kk = t; right = [1, 0, ...right]; continue; }
    // tok_EL_add3 preserves (0 :: right); tok_DR_zero consumes that zero
    // before bounce_DR, so the bounce starts on the suffix 'right'.
    const z = bounceDR(r, [1, v - 3, ...t], right);
    if (z.halt) return z;
    kk = z.a; right = z.right;
  }
  return state("EL", [0, ...right], r.slice());
}

let tokenCalls = 0;
function closeTokDR(r, x) {
  tokenCalls++;
  const z = bounceDR(r, [0], x);
  return z.halt ? z : normalizeEL(z.a, r, z.right);
}
function closeTokCR(r, x) {
  tokenCalls++;
  const z = bounceCR(r, 0, [0], x);
  return z.halt ? z : normalizeEL(z.a, r, z.right);
}

function step(s) {
  const { mode, L, R } = s;
  if (mode === "CR") {
    if (!L.length) return state("EL", [0], bump(R));
    const a = L[0], t = L.slice(1);
    if (a === 0) return state("CR", t, bumpN(R, 2));
    if (a === 1) {
      if (!t.length) return state("EL", [0], [0, ...bumpN(R, 3)]);
      const b = t[0], u = t.slice(1);
      if (b === 0) return state("CR", [1, ...u], [0, 0, ...bump(R)]);
      if (b === 1) {
        if (!u.length) return state("EL", [0, 0, 0, 0], [1, 0, ...R]);
        return state("EL", [0, 0, 0, 0, ...u], [0, 0, ...bump(R)]);
      }
      return state("DR", [0, ...u], [1, b - 2, ...R]);
    }
    return { halt: "CR head >= 2" };
  }
  if (mode === "EL") {
    if (!R.length) return state("CR", L, [0]);
    const a = R[0], t = R.slice(1);
    if (a === 0) return state("EL", [0, ...L], t);
    return state("DL", L, [a - 1, ...t]);
  }
  if (mode === "DL") {
    if (!R.length) return state("CR", L, [2]);
    const a = R[0], t = R.slice(1);
    if (a === 0) return state("EL", [0, ...bump(L)], t);
    if (a === 1) return closeTokDR(t, L);
    return state("DR", L, [1, a - 2, ...t]);
  }
  if (mode === "DR") {
    if (!L.length) return state("EL", [0], R);
    const a = L[0], t = L.slice(1);
    if (!R.length) {
      if (a === 0) return state("EL", bump(t), [0]);
      return state("DR", [a - 1, ...t], [0]);
    }
    const b = R[0], u = R.slice(1);
    // Source mode_DR tokenizes only r1=0. Positive r1 is ordinary;
    // mode_DL has the separate 0/1/>=2 split.
    if (b === 0) return a === 0 ? closeTokDR(u, t) : closeTokCR(u, [a - 1, ...t]);
    if (a === 0) return state("DR", t, [1, b - 1, ...u]);
    return state("CR", [a - 1, ...t], [0, b - 1, ...u]);
  }
  return { halt: "unknown mode" };
}

function run(s, n) {
  for (let i = 0; i < n; i++) {
    s = step(s);
    if (s.halt) throw new Error("halt at offset " + (i + 1) + ": " + s.halt);
  }
  return s;
}
// Exact raw-step counts from the pinned mode_*_closed execute branches.
function sourceClosureCost(s) {
  const { mode, L, R } = s;
  if (mode === "CR") {
    if (!L.length) return 2;
    if (L[0] === 0) return 2;
    if (L[0] === 1) {
      if (!L.slice(1).length) return 6;
      if (L[1] === 0) return 5;
      if (L[1] === 1) return 16;
      return 15;
    }
    throw new Error("halting CR branch");
  }
  if (mode === "EL") {
    if (!R.length) return 1;
    return R[0] === 0 ? 2 : 1;
  }
  if (mode === "DL") {
    if (!R.length) return 4;
    if (R[0] === 0) return 6;
    if (R[0] === 1) throw new Error("DL token closure has no fixed execute cost");
    return 4;
  }
  if (mode === "DR") {
    if (!L.length) return 1;
    if (!R.length) return L[0] === 0 ? 4 : 3;
    if (R[0] === 0) throw new Error("DR token closure has no fixed execute cost");
    return L[0] === 0 ? 4 : 3;
  }
  throw new Error("unknown stack mode");
}

function runWithCost(s, n) {
  let rawSteps = 0;
  for (let i = 0; i < n; i++) {
    rawSteps += sourceClosureCost(s);
    s = step(s);
    if (s.halt) throw new Error("halt at offset " + (i + 1) + ": " + s.halt);
  }
  return { state: s, rawSteps };
}
const Corr = (r, c) => state("DR", [...zeros(r), 1], [1, c]);
const F = r => state("EL", zeros(4), [1, 0, 0, 0, ...repeat([1, 0], r + 2), 3]);
const G = r => state("DR", [0, 0, ...repeat([1, 0], r + 2), 0, 0, 1, 0, 0, 0], [1, 0]);
const H = r => state("CR", [0, ...repeat([1, 0], r + 1), 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0]);

function assertState(label, actual, expected) {
  if (!eq(actual, expected)) {
    throw new Error(label + "\nactual=" + JSON.stringify(actual) + "\nexpected=" + JSON.stringify(expected));
  }
}

let checks = 0;
for (let r = 1; r <= 8; r++) {
  assertState("c=3, r=" + r, run(Corr(r, 3), 2 * r + 14), Corr(r + 4, 0)); checks++;
  assertState("c=6, r=" + r, run(Corr(r, 6), 2 * r + 14), Corr(r + 4, 3)); checks++;
  assertState("c=0, r=" + r, run(Corr(r, 0), 3 * r + 32), Corr(3, 2 * r + 7)); checks++;
  if (r >= 8) {
    assertState("c=2 corrected sweep, r=" + r,
      run(Corr(r, 2), 2 * r + 30),
      state("CR", [...zeros(r - 8), 1], [33])); checks++;
  }
  assertState("c=1, r=" + r, run(Corr(r, 1), 3 * r + 20), F(r)); checks++;
  assertState("F-to-G, r=" + r, run(F(r), 3 * r + 13), G(r)); checks++;
  assertState("G-to-H, r=" + r, run(G(r), 4), H(r)); checks++;
}

// Arbitrary-tail transfer identity, with nonempty U and T.
for (let r = 1; r <= 8; r++) {
  const U = [0, 2], T = [3, 0, 1];
  const start = state("DR", [...zeros(r), 1, ...U], [1, ...T]);
  const expected = state("CR", [0, ...U], [...zeros(r + 2), ...T]);
  assertState("arbitrary-tail transfer, r=" + r, run(start, r + 1), expected);
  checks++;
}

// Exact #85 token-closure outputs. Each tok_EL_1 consumes one leading 1
// in K and prepends one zero to the right word.
for (let n = 0; n <= 32; n++) {
  assertState("closeTokDR 0^" + n, closeTokDR([], zeros(n)),
    state("CR", [...zeros(n + 1), 1], [1]));
  checks++;
  assertState("closeTokDR 0^" + n + "1", closeTokDR([], [...zeros(n), 1]),
    state("CR", [...zeros(n + 4), 1], [1]));
  checks++;
}

// Synthetic #85-side token event from DR([0,0],[1]); not the #490 blank root.
tokenCalls = 0;
const projectedPreToken = runWithCost(state("DR", [0, 0], [1]), 21810);
assertState("projected pre-token state", projectedPreToken.state,
  state("DL", [...zeros(267), 1], [1]));
if (tokenCalls !== 0 || projectedPreToken.rawSteps !== 64565) {
  throw new Error("projected pre-token raw/token count mismatch");
}
checks++;
tokenCalls = 0;
const projectedTokenOutput = step(projectedPreToken.state);
assertState("projected token closure output", projectedTokenOutput,
  state("CR", [...zeros(271), 1], [1]));
if (tokenCalls !== 1) throw new Error("projected token closure count mismatch");
const projectedTokenRaw = 4 + 267 * 4 + 28 + 268 * 2 + 1;
if (projectedTokenRaw !== 1637) throw new Error("projected token raw arithmetic mismatch");
checks++;
tokenCalls = 0;
const projectedPostToken = runWithCost(projectedTokenOutput, 288);
assertState("projected post-token D_0(540)", projectedPostToken.state,
  state("CR", [0], [...zeros(5), 540]));
if (tokenCalls !== 0 || projectedPostToken.rawSteps !== 595) {
  throw new Error("projected post-token raw/token count mismatch");
}
if (projectedPreToken.rawSteps + projectedTokenRaw + projectedPostToken.rawSteps !== 66797) {
  throw new Error("projected-seed-to-D_0(540) raw total mismatch");
}
checks++;
assertState("closeTokCR [1,1]", closeTokCR([], [1, 1]),
  state("CR", [0, 0, 0, 1], [1])); checks++;
assertState("closeTokCR [1,1,2,5]", closeTokCR([], [1, 1, 2, 5]),
  state("CR", [0, 0, 0, 4, 5], [1])); checks++;

assertState("projected #85 seed to Corr(3,3)", run(state("DR", [0, 0], [1]), 24), Corr(3, 3)); checks++;

const rootChain = [
  [Corr(3, 3), 20, Corr(7, 0)],
  [Corr(7, 0), 53, Corr(3, 21)],
  [Corr(3, 21), 20, Corr(7, 18)],
  [Corr(31, 0), 125, Corr(3, 69)],
  [Corr(95, 0), 317, Corr(3, 197)],
  [Corr(263, 2), 556, state("CR", [...zeros(255), 1], [33])],
  [state("CR", [...zeros(255), 1], [33]), 256, state("EL", [0], [0, 546])]
];
for (let i = 0; i < rootChain.length; i++) {
  const [start, n, expected] = rootChain[i];
  assertState("root chain " + i, run(start, n), expected);
  checks++;
}

const D = (n, c) => state("CR", [0], [...zeros(4 * n + 5), c]);
const rootGrowthL = [0, 0, 1, 0, 1, 0, 0, 0, 0, 1];
const rootGrowthB = [16, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0];
const Q = [12, 0, 0, 0];
const HwithRight = (r, R) => state("CR",
  [0, ...repeat([1, 0], r + 1), 0, 0, 1, 0, 0, 0], R);
const repeatQ = n => repeat(Q, n);
const Hright = [2, 0, 0, 0, 0];

// The triangular countdown macro and its exact raw-step cost.
for (let n = 0; n <= 6; n++) {
  for (const c of [3, 4, 5, 10, 540]) {
    tokenCalls = 0;
    const result = runWithCost(D(n, c), 8 * n + 24);
    assertState("countdown D_" + n + "(" + c + ")",
      result.state, D(n + 1, c - 3));
    if (tokenCalls !== 0 || result.rawSteps !== 24 * n + 69) {
      throw new Error("countdown raw/token cost mismatch at n=" + n + " c=" + c);
    }
    checks++;
  }
}

// In this projected #85 chain, EL([0],[0,546]) reaches D_0(540) in 16 successors.
assertState("projected #85 EL-to-D0(540)", run(state("EL", [0], [0, 546]), 16), D(0, 540)); checks++;

// The zero-counter reset is 1,481 outer successors / 2,985 raw TM steps.
tokenCalls = 0;
const resetResult = runWithCost(D(180, 0), 1481);
assertState("D_180(0)-to-D_0(1453)", resetResult.state, D(0, 1453));
if (tokenCalls !== 0 || resetResult.rawSteps !== 2985) {
  throw new Error("D_180 reset raw/token cost mismatch");
}
checks++;
const firstCountdownRaw = Array.from({ length: 180 }, (_, n) => 24 * n + 69)
  .reduce((a, b) => a + b, 0);
const secondCountdownLength = Array.from({ length: 484 }, (_, n) => 8 * n + 24)
  .reduce((a, b) => a + b, 0);
const secondCountdownRaw = Array.from({ length: 484 }, (_, n) => 24 * n + 69)
  .reduce((a, b) => a + b, 0);
if (firstCountdownRaw !== 399060 || secondCountdownLength !== 946704 ||
    secondCountdownRaw !== 2838660) {
  throw new Error("countdown aggregate arithmetic mismatch");
}

// In the projected #85 system, D_484(1) reaches H(1939) by the c=1 corridor: D->F->G->H.
// All three segments are ordinary source branches (no token closure).
const rRoot = 1939;
tokenCalls = 0;
const dToF = runWithCost(D(484, 1), 3897);
assertState("D_484(1)-to-F(1939)", dToF.state, F(rRoot));
if (tokenCalls !== 0 || dToF.rawSteps !== 13641) throw new Error("D-to-F cost mismatch");
checks++;
tokenCalls = 0;
const fToG = runWithCost(F(rRoot), 5830);
assertState("F(1939)-to-G(1939)", fToG.state, G(rRoot));
if (tokenCalls !== 0 || fToG.rawSteps !== 17487) throw new Error("F-to-G cost mismatch");
checks++;
tokenCalls = 0;
const gToH = runWithCost(G(rRoot), 4);
assertState("G(1939)-to-H(1939)", gToH.state, H(rRoot));
if (tokenCalls !== 0 || gToH.rawSteps !== 13) throw new Error("G-to-H cost mismatch");
checks++;

// The 38-successor padding macro removes four (1,0) pairs and prepends Q^2
// to the right stack. It is suffix-parametric and costs 128 raw TM steps.
const opaquePadSuffix = { opaque: "pad-T" };
for (const r of [0, 1, 2, 3, 4, 5, 6, 7, 11, 1935]) {
  for (const suffix of [
    [...Hright, 5, 3, 1],
    [...Hright, opaquePadSuffix],
    [...repeatQ(3), ...Hright, 5, 3, 1]
  ]) {
    tokenCalls = 0;
    const result = runWithCost(HwithRight(r + 4, suffix), 38);
    assertState("H padding r=" + r + " suffix=" + JSON.stringify(suffix),
      result.state, HwithRight(r, [...Q, ...Q, ...suffix]));
    if (tokenCalls !== 0 || result.rawSteps !== 128) {
      throw new Error("H padding raw/token cost mismatch");
    }
    if (suffix.includes(opaquePadSuffix) &&
        result.state.R[result.state.R.length - 1] !== opaquePadSuffix) {
      throw new Error("H padding opaque suffix identity lost");
    }
    checks++;
  }
}

// The 179-successor base macro accepts any positive head a>=2 and
// arbitrary suffix T, prepending [16] and three Q blocks. It costs 591 raw.
const opaqueBaseSuffix = { opaque: "base-T" };
for (const a of [2, 3, 4, 5, 12, 100, 100000]) {
  for (const suffix of [[], [5, 3, 1], [opaqueBaseSuffix]]) {
    tokenCalls = 0;
    const inputRight = [a, ...suffix];
    const result = runWithCost(HwithRight(7, inputRight), 179);
    const expectedTail = [16, 0, 0, 0, ...repeatQ(3), ...inputRight];
    assertState("H base a=" + a + " suffix=" + JSON.stringify(suffix),
      result.state, state("DR", rootGrowthL, [1, ...rootGrowthB, ...expectedTail]));
    if (tokenCalls !== 0 || result.rawSteps !== 591) {
      throw new Error("H base raw/token cost mismatch");
    }
    if (suffix.includes(opaqueBaseSuffix) &&
        result.state.R[result.state.R.length - 1] !== opaqueBaseSuffix) {
      throw new Error("H base opaque suffix identity lost");
    }
    checks++;
  }
}

// Projected #85 H-family entry: 483 padding blocks followed by the 179-step base.
// H(1939) -> H(7, Q^966 ++ [2,0,0,0,0]) -> DR/G/B seed.
tokenCalls = 0;
const hPadding = runWithCost(H(rRoot), 38 * 483);
assertState("H(1939)-to-padded-H(7)", hPadding.state,
  HwithRight(7, [...repeatQ(966), ...Hright]));
if (tokenCalls !== 0 || hPadding.rawSteps !== 61824) {
  throw new Error("projected H-padding aggregate mismatch");
}
checks++;
tokenCalls = 0;
const rootGrowthEntryResult = runWithCost(hPadding.state, 179);
const rootGrowthEntryTail = [16, 0, 0, 0, ...repeatQ(969), ...Hright];
assertState("projected first DR/G/B seed", rootGrowthEntryResult.state,
  state("DR", rootGrowthL, [1, ...rootGrowthB, ...rootGrowthEntryTail]));
if (tokenCalls !== 0 || rootGrowthEntryResult.rawSteps !== 591) {
  throw new Error("projected H-base aggregate mismatch");
}
checks++;
const rootGrowth = rootGrowthEntryResult.state;
const rootEntryOuter = 3897 + 5830 + 4 + 38 * 483 + 179;
const rootEntryRaw = 13641 + 17487 + 13 + 61824 + 591;
if (rootEntryOuter !== 28264 || rootEntryRaw !== 93556 || rootGrowth.R.length !== 3898) {
  throw new Error("projected first-entry aggregate mismatch");
}

// The earlier 50,000-successor checkpoint is the first seed plus 286
// repetitions of the 76-successor insertion macro.
tokenCalls = 0;
const laterRootCheckpoint = runWithCost(rootGrowth, 286 * 76);
if (tokenCalls !== 0 || laterRootCheckpoint.rawSteps !== 72644 ||
    laterRootCheckpoint.state.R.length !== 7330 ||
    !eq(laterRootCheckpoint.state.L, rootGrowthL) ||
    !eq(laterRootCheckpoint.state.R.slice(0, 13), [1, ...rootGrowthB])) {
  throw new Error("286-loop projected growth checkpoint mismatch");
}
if (rootEntryOuter + 286 * 76 !== 50000 ||
    rootEntryRaw + laterRootCheckpoint.rawSteps !== 166200) {
  throw new Error("50,000-step projected growth checkpoint aggregate mismatch");
}
checks++;

// The 76-step projected growth macro is tail-parametric and never calls a token
// normalizer: it inserts one copy of B immediately after the leading 1.
for (const T of [
  [], [0], [1], [2, 4, 6, 8], [3, 0, 0], [7, 5, 3, 1],
  [12, 0, 0, 0, 12, 0, 0, 0, 2]
]) {
  tokenCalls = 0;
  const result = runWithCost(state("DR", rootGrowthL, [1, ...rootGrowthB, ...T]), 76);
  assertState("projected growth 76, suffix=" + JSON.stringify(T), result.state,
    state("DR", rootGrowthL, [1, ...rootGrowthB, ...rootGrowthB, ...T]));
  if (tokenCalls !== 0) throw new Error("projected growth 76 unexpectedly called a token normalizer");
  if (result.rawSteps !== 254) throw new Error("projected growth 76 raw-step count mismatch: " + result.rawSteps);
  checks++;
}

// Check the actual root-reachable state one growth step, retaining its entire
// pre-existing suffix untouched.
tokenCalls = 0;
const grownRootResult = runWithCost(rootGrowth, 76);
assertState("projected growth actual 76-step state", grownRootResult.state,
  state("DR", rootGrowthL, [1, ...rootGrowthB, ...rootGrowthB, ...rootGrowth.R.slice(13)]));
if (tokenCalls !== 0) throw new Error("projected growth step called a token normalizer");
if (grownRootResult.rawSteps !== 254) throw new Error("projected growth raw-step count mismatch");
checks++;

// A genuinely opaque suffix must remain the same object, not merely serialize
// to an equal numeric list.
const opaqueSuffix = { opaque: "T" };
tokenCalls = 0;
const opaqueResult = runWithCost(state("DR", rootGrowthL, [1, ...rootGrowthB, opaqueSuffix]), 76);
assertState("projected growth opaque suffix", opaqueResult.state,
  state("DR", rootGrowthL, [1, ...rootGrowthB, ...rootGrowthB, opaqueSuffix]));
if (opaqueResult.state.R[opaqueResult.state.R.length - 1] !== opaqueSuffix) {
  throw new Error("opaque suffix identity was not preserved");
}
if (tokenCalls !== 0 || opaqueResult.rawSteps !== 254) {
  throw new Error("opaque-suffix macro token/raw-step audit failed");
}
checks++;

// The separate H-phase CR 76-successor identity also has an independently
// derived raw-step count; it is not used as a substitute for DR/G/B.
const P = [0, 0, 1, 0, 19];
const HB = [0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 16];
const U = [0, 0, 0, 12, 0, 0, 0, 12, 0, 0, 0, 12, 0, 0, 0, 2, 0, 0, 0, 0];
tokenCalls = 0;
const hPhaseResult = runWithCost(state("CR", [1, 0], [...P, ...HB, ...U]), 76);
assertState("H-phase CR 76-step insertion", hPhaseResult.state,
  state("CR", [1, 0], [...P, ...HB, ...HB, ...U]));
if (tokenCalls !== 0 || hPhaseResult.rawSteps !== 254) {
  throw new Error("H-phase 76-step token/raw-step audit failed");
}
checks++;

console.log(JSON.stringify({
  ok: true, checks,
  projectedGrowth76RawSteps: grownRootResult.rawSteps,
  opaqueGrowth76RawSteps: opaqueResult.rawSteps,
  hPhase76RawSteps: hPhaseResult.rawSteps
}, null, 2));
