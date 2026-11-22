#!/usr/bin/env node
// Fast persistent-list interpreter for the source-derived outer stack successor.
// Run: node fast_root_stack_sim.js [macro-steps]
// This is experimental computational evidence, not a proof of nonhalting.

const steps = Number(process.argv[2] ?? 1_000_000);
let nodeId = 0;

function cons(v, next = null) {
  return {
    id: ++nodeId, v, next,
    len: 1 + (next?.len ?? 0),
    nz: (v === 0 ? 0 : 1) + (next?.nz ?? 0),
    ones: (v === 1 ? 1 : 0) + (next?.ones ?? 0),
    max: Math.max(v, next?.max ?? 0),
    binary: v <= 1 && (next?.binary ?? true),
    // Z1 = 0*(epsilon | 1)
    z1: v === 0 ? (next?.z1 ?? true) : v === 1 ? next === null : false,
    firstNZ: v !== 0 ? v : (next?.firstNZ ?? null),
  };
}
function fromArray(xs, tail = null) {
  let p = tail;
  for (let i = xs.length - 1; i >= 0; --i) p = cons(xs[i], p);
  return p;
}
function bump(xs) { return xs ? cons(xs.v + 1, xs.next) : cons(1); }
function bumpN(xs, n) { for (let i = 0; i < n; ++i) xs = bump(xs); return xs; }
function take(xs, n = 12) {
  const out = [];
  while (xs && out.length < n) { out.push(xs.v); xs = xs.next; }
  return out;
}
const halted = reason => ({ halt: reason });
const stats = { bounceCR: 0, bounceDR: 0, tokenEventCount: 0, tokenEvents: [] };

function bounceCR(r3, k0, kAcc, right, depth = 0) {
  while (right) {
    if (depth++ > 200_000) return halted("bounceCR recursion guard");
    stats.bounceCR++;
    const a = right.v, rest = right.next;
    if (a === 0) { k0 += 2; right = rest; continue; }
    if (a === 1) {
      if (!rest) return [cons(k0 + 1, kAcc), fromArray([0, 0, 1])];
      const b = rest.v, rest2 = rest.next;
      if (b === 0) { kAcc = cons(k0 + 4, kAcc); k0 = 0; right = rest2; continue; }
      if (b === 1) {
        // tok_CR_1_1_nil_25 / tok_CR_1_1_cons_25 return 0 :: 0 :: ...;
        // this function stores the suffix after the leading 0 of tok_EL.
        if (!rest2) return [cons(k0 + 1, kAcc), fromArray([0, 1])];
        return [cons(k0 + 1, kAcc), fromArray([0, rest2.v + 2], rest2.next)];
      }
      return bounceDR(r3, cons(1, cons(k0 + 1, kAcc)), cons(b - 2, rest2), depth + 1);
    }
    return halted("tok_CR add2 branch");
  }
  if (k0 === 0) return [kAcc, cons(1)];
  if (k0 === 1) return [cons(0, kAcc), fromArray([0, 1])];
  if (k0 === 2) return [cons(1, kAcc), fromArray([0, 1])];
  return [cons(k0 - 1, kAcc), fromArray([0, 1])];
}

function bounceDR(r3, kAcc, right, depth = 0) {
  while (right) {
    if (depth++ > 200_000) return halted("bounceDR recursion guard");
    stats.bounceDR++;
    const a = right.v, rest = right.next;
    if (a === 0) { kAcc = cons(1, kAcc); right = rest; continue; }
    if (a === 1 && !rest) return [cons(1, kAcc), fromArray([0, 0, 1])];
    return bounceCR(r3, 0, cons(1, kAcc), cons(a - 1, rest), depth + 1);
  }
  return [kAcc, cons(1)];
}

function normalizeEL(k, r3, rightTail, depth = 0) {
  while (k) {
    if (depth++ > 200_000) return halted("normalizeEL recursion guard");
    const a = k.v, rest = k.next;
    if (a === 0) {
      if (!rest) return { mode: "CR", L: cons(0, rightTail), R: bump(r3) };
      const z = bounceCR(r3, rest.v + 2, rest.next, rightTail);
      if (z.halt) return z;
      k = z[0]; rightTail = z[1]; continue;
    }
    if (a === 1) {
      // Source tok_EL_1: tok_EL (1 :: K) R3 (0 :: L) -> tok_EL K R3 (0 :: 0 :: L).
      k = rest; rightTail = cons(0, rightTail); continue;
    }
    if (a === 2) { k = rest; rightTail = cons(1, cons(0, rightTail)); continue; }
    // bl_step_macro_len composes tok_EL_add3 on (0 :: rightTail) with
    // tok_DR_zero, so bounceDR starts on rightTail after that zero is consumed.
    const z = bounceDR(r3, cons(1, cons(a - 3, rest)), rightTail);
    if (z.halt) return z;
    k = z[0]; rightTail = z[1];
  }
  return { mode: "EL", L: cons(0, rightTail), R: r3 };
}

function closeTokDR(r3, L, macro) {
  stats.tokenEventCount++;
  if (stats.tokenEvents.length < 12) {
    stats.tokenEvents.push({
      macro, kind: "DR", inputLength: L?.len ?? 0, inputOnes: L?.ones ?? 0,
      inputHead: take(L, 12), r3Head: take(r3, 8),
    });
  }
  const z = bounceDR(r3, cons(0), L);
  return z.halt ? z : normalizeEL(z[0], r3, z[1]);
}
function closeTokCR(r3, L, macro) {
  stats.tokenEventCount++;
  if (stats.tokenEvents.length < 12) {
    stats.tokenEvents.push({
      macro, kind: "CR", inputLength: L?.len ?? 0, inputOnes: L?.ones ?? 0,
      inputHead: take(L, 12), r3Head: take(r3, 8),
    });
  }
  const z = bounceCR(r3, 0, cons(0), L);
  return z.halt ? z : normalizeEL(z[0], r3, z[1]);
}

function successor(c, macro) {
  const { mode, L, R } = c;
  if (mode === "CR") {
    if (!L) return { mode: "EL", L: cons(0), R: bump(R) };
    const a = L.v, t = L.next;
    if (a === 0) return { mode: "CR", L: t, R: bumpN(R, 2) };
    if (a === 1) {
      if (!t) return { mode: "EL", L: cons(0), R: cons(0, bumpN(R, 3)) };
      const b = t.v, r = t.next;
      if (b === 0) return { mode: "CR", L: cons(1, r), R: cons(0, cons(0, bump(R))) };
      if (b === 1) {
        if (!r) return { mode: "EL", L: fromArray([0, 0, 0, 0]), R: fromArray([1, 0], R) };
        return { mode: "EL", L: fromArray([0, 0, 0, 0], r), R: cons(0, cons(0, bump(R))) };
      }
      return { mode: "DR", L: cons(0, r), R: cons(1, cons(b - 2, R)) };
    }
    return halted("mode_CR head >= 2");
  }

  if (mode === "EL") {
    if (!R) return { mode: "CR", L, R: cons(0) };
    const a = R.v, t = R.next;
    if (a === 0) return { mode: "EL", L: cons(0, L), R: t };
    return { mode: "DL", L, R: cons(a - 1, t) };
  }

  if (mode === "DL") {
    if (!R) return { mode: "CR", L, R: cons(2) };
    const a = R.v, t = R.next;
    if (a === 0) return { mode: "EL", L: cons(0, bump(L)), R: t };
    if (a === 1) return closeTokDR(t, L, macro);
    return { mode: "DR", L, R: cons(1, cons(a - 2, t)) };
  }

  if (mode === "DR") {
    if (!L) return { mode: "EL", L: cons(0), R };
    const a = L.v, lt = L.next;
    if (!R) {
      if (a === 0) return { mode: "EL", L: bump(lt), R: cons(0) };
      return { mode: "DR", L: cons(a - 1, lt), R: cons(0) };
    }
    const b = R.v, rt = R.next;
    // Source mode_DR tokenizes only r1=0; every positive r1 takes
    // the ordinary DR/CR branch (unlike mode_DL, which splits 0/1/>=2).
    if (b === 0) {
      if (a === 0) return closeTokDR(rt, lt, macro);
      return closeTokCR(rt, cons(a - 1, lt), macro);
    }
    if (a === 0) return { mode: "DR", L: lt, R: cons(1, cons(b - 1, rt)) };
    return { mode: "CR", L: cons(a - 1, lt), R: cons(0, cons(b - 1, rt)) };
  }
  return halted("unknown mode");
}

// Empirical candidate invariant. Z1 is the regular language 0*(epsilon | 1).
function invariantFailures(c) {
  const { mode, L, R } = c;
  const rh = R?.v, tailNZ = R?.next?.firstNZ;
  const z1Bump = !L || (L.v === 0 && !L.next);
  const failures = [];
  // The corrected root cycle has the legitimate exceptional state CR(L=[1]).
  // All other states in this orbit keep L in Z1 = 0*(epsilon | 1).
  if (L && !L.z1 && !(mode === "CR" && L.len === 1 && L.v === 1)) {
    failures.push("L is not in Z1 or the exceptional CR([1]) state");
  }
  if ((R?.nz ?? 0) > 2) failures.push("R has more than two nonzero entries");
  if (L && !L.binary) failures.push("L contains a value outside {0,1}");
  if (mode === "DR" && (!R || rh === 0)) failures.push("DR right head is not positive");
  if (mode === "EL" && rh === 1 && (!L || L.v !== 0)) failures.push("EL/right-head-1 requires L to start 0");
  if (mode === "EL" && R?.firstNZ === 2 && !(L?.z1 ?? true)) failures.push("EL/first-nonzero-2 requires L in Z1");
  if (mode === "EL" && rh === 1 && tailNZ === 2 && !z1Bump) failures.push("EL/1...2 requires L empty or [0]");
  if (mode === "DL" && rh === 0 && (!L || L.v !== 0)) failures.push("DL/right-head-0 requires L to start 0");
  if (mode === "DL" && rh === 1 && !(L?.z1 ?? true)) failures.push("DL/right-head-1 requires L in Z1");
  if (mode === "DL" && rh === 0 && tailNZ === 2 && !z1Bump) failures.push("DL/0...2 requires L empty or [0]");
  if (mode === "CR" && L?.v === 1 && L.next?.v === 1 && rh === 1 && !(L.next.next?.z1 ?? true)) {
    failures.push("CR/11 with right-head-1 requires L.drop(2) in Z1");
  }
  return failures;
}

let c = { mode: "DR", L: fromArray([0, 0]), R: fromArray([1]) };
let haltAt = null, invariantViolation = null;
let maxLeftLength = 0, maxRightLength = 0, maxEntry = 0, maxLeftOnes = 0;
let maxLeftNonzeros = 0, maxRightNonzeros = 0;
let minDRRightHead = Infinity;
for (let i = 0; i < steps; ++i) {
  const failures = invariantFailures(c);
  if (failures.length) {
    invariantViolation = { macro: i, failures, state: { mode: c.mode, L: take(c.L, 20), R: take(c.R, 20) } };
    break;
  }
  maxLeftLength = Math.max(maxLeftLength, c.L?.len ?? 0);
  maxRightLength = Math.max(maxRightLength, c.R?.len ?? 0);
  maxEntry = Math.max(maxEntry, c.L?.max ?? 0, c.R?.max ?? 0);
  maxLeftOnes = Math.max(maxLeftOnes, c.L?.ones ?? 0);
  maxLeftNonzeros = Math.max(maxLeftNonzeros, c.L?.nz ?? 0);
  maxRightNonzeros = Math.max(maxRightNonzeros, c.R?.nz ?? 0);
  if (c.mode === "DR") minDRRightHead = Math.min(minDRRightHead, c.R?.v ?? Infinity);
  const next = successor(c, i);
  if (next.halt) {
    haltAt = { macro: i, reason: next.halt, state: { mode: c.mode, L: take(c.L, 20), R: take(c.R, 20) } };
    break;
  }
  c = next;
}
console.log(JSON.stringify({
  requestedMacroSteps: steps,
  completedMacroSteps: invariantViolation?.macro ?? haltAt?.macro ?? steps,
  haltAt, invariantViolation,
  tokenEventCount: stats.tokenEventCount,
  tokenEvents: stats.tokenEvents,
  bounceCRCalls: stats.bounceCR, bounceDRCalls: stats.bounceDR,
  maxLeftLength, maxRightLength, maxEntry, maxLeftOnes,
  maxLeftNonzeros, maxRightNonzeros, minDRRightHead,
  finalState: {
    mode: c.mode, leftLength: c.L?.len ?? 0, rightLength: c.R?.len ?? 0,
    leftOnes: c.L?.ones ?? 0, leftHead: take(c.L, 16), rightHead: take(c.R, 16),
  },
}, null, 2));
