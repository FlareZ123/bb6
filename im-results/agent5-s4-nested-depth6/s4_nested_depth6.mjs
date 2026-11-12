#!/usr/bin/env node
"use strict";

// Reproduce the first six S4 suffix-renormalization levels.
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
function mass(xs) { return xs.reduce((s, x) => s + x + 1n, 0n); }

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

function gate(c, xs) {
  const out = [];
  let a = xs.length === 0 ? c - 1n : xs[0] + c;
  let i = xs.length === 0 ? 0 : 1;

  while (i < xs.length && (a & 1n) === 1n) {
    out.push(a / 2n);
    a = xs[i] + a / 2n + 1n;
    i++;
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
  for (const c of word) {
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

console.log(JSON.stringify({
  levels: {
    Q: qMass, R: rMass, V: vMass, W: wMass, X: xMass, Y: yMass
  },
  prefixCycles: {
    V_eightDigit: vCycle,
    W_sevenDigit: wCycle,
    X_eightDigit: xCycle
  },
  states: {
    rStar: show(rStar),
    sStar: show(sStar),
    afterV: show(tailAfterV),
    afterW: show(tailAfterW),
    afterX: show(tailAfterX),
    afterY: show(tailAfterY)
  }
}, null, 2));
