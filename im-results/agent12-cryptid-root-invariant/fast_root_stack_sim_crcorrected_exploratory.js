#!/usr/bin/env node
/*
 * Exploratory source-corrected #85/#490 root replay.
 *
 * The ordinary CR clauses below were corrected on 2026-11-22 against the
 * pinned #85 mode_CR_n_n_closed source:
 *   CR 1,0   -> CR(L8, 0 :: bump^3(R))
 *   CR 1,1   -> EL(bump(L8), [1,0,0] ++ R)
 *   CR 1,b>=2 -> DR((b-2) :: L8, [1,0,0] ++ R)
 * The empty bump is [0], matching bumpPairHead [] = [(0,0)].
 *
 * IMPORTANT: this is still only an exploratory projected simulator.
 * bounceCR/bounceDR/normalizeEL are a JS port of the pinned token-normalizer
 * proofs and have not yet been independently audited end-to-end or connected
 * to raw ReachesPlus. Do not treat this run as a proof of halting/nonhalting.
 */

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
    z1: v === 0 ? (next?.z1 ?? true) : v === 1 ? next === null : false,
    firstNZ: v !== 0 ? v : (next?.firstNZ ?? null),
  };
}

function fromArray(xs, tail = null) {
  let p = tail;
  for (let i = xs.length - 1; i >= 0; --i) p = cons(xs[i], p);
  return p;
}
function bump(xs) { return xs ? cons(xs.v + 1, xs.next) : cons(0); }
function bumpN(xs, n) { for (let i = 0; i < n; ++i) xs = bump(xs); return xs; }
function take(xs, n = 12) {
  const out = [];
  while (xs && out.length < n) { out.push(xs.v); xs = xs.next; }
  return out;
}
function takeLast(xs, n = 12) {
  const out = [];
  while (xs) {
    if (out.length === n) out.shift();
    out.push(xs.v);
    xs = xs.next;
  }
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
    if (a === 1) { k = rest; rightTail = cons(0, rightTail); continue; }
    if (a === 2) { k = rest; rightTail = cons(1, cons(0, rightTail)); continue; }
    const z = bounceDR(r3, cons(1, cons(a - 3, rest)), rightTail);
    if (z.halt) return z;
    k = z[0]; rightTail = z[1];
  }
  return { mode: "EL", L: cons(0, rightTail), R: r3 };
}

function closeTokDR(r3, L, macro) {
  stats.tokenEventCount++;
  if (stats.tokenEvents.length < 20) stats.tokenEvents.push({
    macro, kind: "DR", inputLength: L?.len ?? 0, inputHead: take(L, 12), r3Head: take(r3, 8),
  });
  const z = bounceDR(r3, cons(0), L);
  return z.halt ? z : normalizeEL(z[0], r3, z[1]);
}
function closeTokCR(r3, L, macro) {
  stats.tokenEventCount++;
  if (stats.tokenEvents.length < 20) stats.tokenEvents.push({
    macro, kind: "CR", inputLength: L?.len ?? 0, inputHead: take(L, 12), r3Head: take(r3, 8),
  });
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
      if (b === 0) return { mode: "CR", L: r, R: cons(0, bumpN(R, 3)) };
      if (b === 1) return { mode: "EL", L: bump(r), R: fromArray([1, 0, 0], R) };
      return { mode: "DR", L: cons(b - 2, r), R: fromArray([1, 0, 0], R) };
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
    if (b === 0) {
      if (a === 0) return closeTokDR(rt, lt, macro);
      return closeTokCR(rt, cons(a - 1, lt), macro);
    }
    if (a === 0) return { mode: "DR", L: lt, R: cons(1, cons(b - 1, rt)) };
    return { mode: "CR", L: cons(a - 1, lt), R: cons(0, cons(b - 1, rt)) };
  }
  return halted("unknown mode");
}

let s = { mode: "DR", L: fromArray([0, 0]), R: fromArray([1]) };
let macro = 0, haltedAt = null, checkpoints = [];
for (; macro < steps; ++macro) {
  if (macro % Math.max(1, Math.floor(steps / 10)) === 0) checkpoints.push({
    macro, mode: s.mode, Llen: s.L?.len ?? 0, Rlen: s.R?.len ?? 0,
    Lhead: take(s.L, 10), Rhead: take(s.R, 10),
    Ltail: takeLast(s.L, 5), Rtail: takeLast(s.R, 5),
  });
  const z = successor(s, macro);
  if (z.halt) { haltedAt = { macro, reason: z.halt, state: { mode: s.mode, L: take(s.L, 24), R: take(s.R, 24) } }; break; }
  s = z;
}

console.log(JSON.stringify({
  requestedSteps: steps, completedSteps: macro, haltedAt,
  final: { mode: s.mode, Llen: s.L?.len ?? 0, Rlen: s.R?.len ?? 0,
    Lhead: take(s.L, 24), Rhead: take(s.R, 24),
    Ltail: takeLast(s.L, 10), Rtail: takeLast(s.R, 10) },
  stats, checkpoints,
}, null, 2));
