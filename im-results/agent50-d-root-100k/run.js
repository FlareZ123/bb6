#!/usr/bin/env node
// Independent JavaScript port of im-results/agent3-d-density-drift/evaluator.py.
// Exact BigInt arithmetic; the return-map rules and canonical suffix convention
// are copied from that source. Default: 100000 total-return iterations per root.

const RULES = [
  [1, 1, 1], [0, 1, 4], [1, -1, 2], [0, 1, 0],
  [1, -1, 0], [1, -1, 3], [1, -1, 2], [1, -1, 5],
  [0, -1, 2], [0, -1, 1], [1, -1, 4], null,
];
const D = [3n, 4n, 2n];
const LIMIT = Number(process.argv[2] || 100000);
const exitCache = new Map();
const stepCache = new Map();

function trim0(w) {
  let i = w.length;
  while (i > 0 && w[i - 1] === "0") i--;
  return w.slice(0, i);
}
function canon(w) {
  w = trim0(w);
  let q = 0;
  while (q < w.length && w[q] === "1") q++;
  return [q, w.slice(q)];
}
function firstExit(q, w) {
  const key = q + "|" + w;
  if (exitCache.has(key)) return exitCache.get(key);
  const left = [];
  while (true) {
    const b = w.length ? Number(w[0]) : 0;
    const z = w.length ? w.slice(1) : "";
    const ins = RULES[2 * q + b];
    if (ins === null) {
      exitCache.set(key, null);
      return null;
    }
    let [write, dir, next] = ins;
    write = String(write);
    q = next;
    if (dir === 1) {
      left.push(write);
      w = z;
    } else {
      const y = write + z;
      if (left.length === 0) {
        const ans = [q, trim0(y)];
        exitCache.set(key, ans);
        return ans;
      }
      w = left.pop() + y;
    }
  }
}
function eStep(w) {
  const key = "E|" + w;
  if (stepCache.has(key)) return stepCache.get(key);
  let q = 4;
  const guard = "00101010";
  for (let p = 0; p <= guard.length; p++) {
    if (p >= 2 && p % 2 === 0 && (q === 1 || q === 3) && !w.startsWith("1")) {
      const [l, s] = canon(w.slice(1));
      const ans = [11 - p + l, s];
      stepCache.set(key, ans);
      return ans;
    }
    if (q === 5 && w.startsWith("1")) {
      stepCache.set(key, null);
      return null;
    }
    if (p === guard.length) throw new Error("E guard");
    const a = firstExit(q, w);
    if (a === null) {
      stepCache.set(key, null);
      return null;
    }
    q = a[0];
    w = trim0(guard[p] + a[1]);
  }
}
function step(w, r) {
  const key = r + "|" + w;
  if (stepCache.has(key)) return stepCache.get(key);
  let ans;
  if (r === 2) {
    const [l, s] = canon(w.slice(1));
    ans = [9 + l, s];
  } else if (r === 1) {
    ans = eStep(w);
  } else {
    let v = w.slice(1), c = 0;
    while (v.startsWith("1")) {
      const z = v + "000";
      if (z.startsWith("10")) {
        v = v.slice(2);
        c += 2;
      } else if (z.startsWith("111")) {
        v = v.slice(3);
        c += 8;
      } else {
        const e = eStep(trim0("0" + v.slice(3)));
        ans = e === null ? null : [e[0] + c + 2, e[1]];
        stepCache.set(key, ans);
        return ans;
      }
    }
    const [l, s] = canon(v.slice(1));
    ans = [11 + c + l, s];
  }
  stepCache.set(key, ans);
  return ans;
}
function runRoot(seed) {
  let n = BigInt(seed), w = "";
  const residueCounts = [0, 0, 0];
  const suffixes = new Set();
  let maxSuffixLength = 0, emptySuffixCount = 0;
  const anchors = {};
  for (let i = 0; i < LIMIT; i++) {
    const r = Number(n % 3n);
    residueCounts[r]++;
    const a = step(w, r);
    if (a === null) {
      return {
        seed, iterations: i, terminalAt: i, finalNBits: n.toString(2).length,
        finalSuffix: w, residueCounts, maxSuffixLength,
        distinctSuffixes: suffixes.size, emptySuffixCount, anchors,
      };
    }
    const c = BigInt(a[0]);
    w = a[1];
    n = 8n * ((n - D[r]) / 3n) + c;
    suffixes.add(w);
    maxSuffixLength = Math.max(maxSuffixLength, w.length);
    if (w === "") emptySuffixCount++;
    if (i + 1 === 9 || i + 1 === 10) {
      anchors[i + 1] = { n: String(n), suffix: w };
    }
  }
  return {
    seed, iterations: LIMIT, terminalAt: null, finalNBits: n.toString(2).length,
    finalSuffix: w, residueCounts, maxSuffixLength,
    distinctSuffixes: suffixes.size, emptySuffixCount, anchors,
  };
}

console.log(JSON.stringify({
  source: "im-results/agent3-d-density-drift/evaluator.py",
  arithmetic: "BigInt exact",
  roots: [9, 5, 15, 39].map(runRoot),
}, null, 2));
