#!/usr/bin/env node
"use strict";

// Deterministic discovery script for the Raw10 two-hole residual box.
// Transition code: 0 = halt; otherwise 1 + 4*next + 2*write + right.
// Z state: q, absolute head coordinate, l (scanned cell then cells left),
// r (cells right of head). This mirrors SparseZipper.move and ZipAuditCore.

const PREFIX = [8, 14, 11, 7, 17, 4, 9, 2, 23, 15];
const F0_DOMAIN = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 24];
const BRANCH_F0 = [12, 22, 24];

function move(z, code) {
  const n = code - 1;
  const next = Math.floor(n / 4);
  const rem = n % 4;
  const write = Math.floor(rem / 2) === 1;
  const right = rem % 2 === 1;
  if (right) {
    return {
      q: next,
      h: z.h + 1,
      l: [z.r[0] ?? false, write, ...z.l.slice(1)],
      r: z.r.slice(1),
    };
  }
  return {
    q: next,
    h: z.h - 1,
    l: z.l.slice(1),
    r: [write, ...z.r],
  };
}

function step(z, table) {
  const code = table[2 * z.q + (z.l[0] ? 1 : 0)];
  if (code === null || code === 0) return null;
  return move(z, code);
}

function runPath(table, maxSteps) {
  let z = { q: 0, h: 0, l: [], r: [] };
  const path = [z];
  let stop = null;
  for (let i = 0; i < maxSteps; i++) {
    const code = table[2 * z.q + (z.l[0] ? 1 : 0)];
    if (code === null) {
      stop = { kind: "undefined", step: i, q: z.q, symbol: z.l[0] ?? false };
      break;
    }
    if (code === 0) {
      stop = { kind: "halt", step: i, q: z.q, symbol: z.l[0] ?? false };
      break;
    }
    z = move(z, code);
    path.push(z);
  }
  if (stop === null) stop = { kind: "cap", step: maxSteps };
  return { path, stop };
}

function trimFalse(xs) {
  let n = xs.length;
  while (n > 0 && xs[n - 1] === false) n--;
  return xs.slice(0, n);
}

function padEq(a, b) {
  a = trimFalse(a);
  b = trimFalse(b);
  return a.length === b.length && a.every((x, i) => x === b[i]);
}

function padEqPrefix(a, b, n) {
  for (let i = 0; i < n; i++) {
    if ((a[i] ?? false) !== (b[i] ?? false)) return false;
  }
  return true;
}

// First certificate found in the stated deterministic search order:
// entry ascending, period ascending, boundary offset ascending, right=false/true.
function findZip(path, maxEntry, maxPeriod, maxOffset) {
  for (let entry = 10; entry < Math.min(maxEntry, path.length - 1); entry++) {
    const c = path[entry];
    for (let period = 1; period <= maxPeriod && entry + period < path.length; period++) {
      const d = path[entry + period];
      if (c.q !== d.q) continue;
      const delta = d.h - c.h;
      for (let offset = -maxOffset; offset <= maxOffset; offset++) {
        for (const right of [false, true]) {
          const boundary = c.h + offset;
          const window = path.slice(entry, entry + period);
          const sideOK = window.every(z => right ? z.h >= boundary : z.h <= boundary);
          if (!sideOK || !(right ? delta >= 0 : delta <= 0)) continue;

          // Int.toNat semantics: negative differences truncate to zero.
          const n = right ? Math.max(0, c.h - boundary) + 1 : Math.max(0, boundary - c.h);
          const tailsOK = right
            ? padEqPrefix(c.l, d.l, n) && padEq(c.r, d.r)
            : padEq(c.l, d.l) && padEqPrefix(c.r, d.r, n);

          if (tailsOK) return { entry, period, right, boundary, delta };
        }
      }
    }
  }
  return null;
}

function tableWith(f0, f1 = null) {
  const t = [...PREFIX, f0, f1];
  if (t.length !== 12) throw new Error("bad table length");
  return t;
}

function f0Leaves() {
  const codes = F0_DOMAIN.filter(x => !BRANCH_F0.includes(x) && x !== 0);
  return codes.map(f0 => {
    const { path, stop } = runPath(tableWith(f0), 120);
    return { f0, stop, zip: findZip(path, 1000, 100, 40) };
  });
}

function branchLeaves() {
  const zip = [], halt = [], open = [];
  for (const f0 of BRANCH_F0) {
    for (let f1 = 0; f1 < 25; f1++) {
      const { path, stop } = runPath(tableWith(f0, f1), 2000);
      if (stop.kind === "halt") {
        halt.push({ f0, f1, steps: stop.step });
        continue;
      }
      const cert = findZip(path, 1500, 100, 10);
      if (cert) zip.push({ f0, f1, ...cert });
      else open.push({ f0, f1 });
    }
  }
  return { zip, halt, open };
}

function extendedOpenSearch(pairs) {
  return pairs.map(({ f0, f1 }) => {
    const { path, stop } = runPath(tableWith(f0, f1), 2300);
    return { f0, f1, stop, extendedZip: findZip(path, 2000, 300, 100) };
  });
}

function stubbornOneHoleLeaves() {
  return [1, 14].map(f0 => {
    const { path, stop } = runPath(tableWith(f0), 100000);
    return { f0, stop, zip: findZip(path, 1000, 100, 40) };
  });
}

const f0 = f0Leaves();
const branches = branchLeaves();
const extended = extendedOpenSearch(branches.open);
const stubborn = stubbornOneHoleLeaves();

const summary = {
  prefixCodes: PREFIX,
  f0Domain: F0_DOMAIN,
  f0ZipLeaves: f0,
  branchZipLeaves: branches.zip,
  branchHaltLeaves: branches.halt,
  branchOpenLeaves: branches.open,
  extendedOpenSearch: extended,
  stubbornOneHoleLeaves: stubborn,
  counts: {
    residualCompletions: F0_DOMAIN.length * 25,
    f0ZipCompletions: f0.filter(x => x.zip).length * 25,
    branchZipCompletions: branches.zip.length,
    nonhaltingCompletions: f0.filter(x => x.zip).length * 25 + branches.zip.length,
    observedHaltingCompletions: 25 + branches.halt.length,
    openCompletions: 2 * 25 + branches.open.length,
    partitionTotal: f0.filter(x => x.zip).length * 25 + branches.zip.length + 25 + branches.halt.length + 2 * 25 + branches.open.length,
  },
};

process.stdout.write(JSON.stringify(summary, null, 2) + "\n");
