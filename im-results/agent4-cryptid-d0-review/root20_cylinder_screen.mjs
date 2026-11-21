#!/usr/bin/env node
// Exact BigInt screen of the authentic-root DRegular chain through episode 20.
// Intermediate computational evidence only; this is not a Lean source proof.

const C = 1975700577069254261393123959451562008800234946348086n;
const M = 3n ** 108n;
const L = (a, q = 0, b = 0) => ({ a: BigInt(a), q, b });

function nextRegular(s) {
  const { a, q, b } = s;
  const r = Number(a % 3n);
  if (r === 2) {
    const k = (a - 2n) / 3n;
    if (q === 0) return L(8n * k + 9n);
    if (q === 1) return L(8n * k + 10n + BigInt(b));
    return L(8n * k + 10n, q - 1, b);
  }
  if (r === 0) {
    const k = (a - 3n) / 3n;
    if (q === 0) return L(8n * k + 11n);
    const d = BigInt(q - 1 + 4 * Math.floor((b + 1) / 3));
    const rem = (b + 1) % 3;
    if (rem === 0) return L(8n * k + 11n + 2n * d);
    if (rem === 1) return L(8n * k + 13n + 2n * d);
    return L(8n * k + 7n + 2n * d, 1, 5);
  }
  const k = (a - 4n) / 3n;
  if (q === 0) return L(8n * k + 5n, 1, 5);
  if (b === 0) return L(8n * k + 5n, 1, 2 * q + 5);
  if (b === 1) return null;
  if (b === 2) return L(8n * k + 9n, q + 1);
  return L(8n * k + 9n, q + 2, b - 3);
}

function secondOfException(s) {
  const k = (s.a - 4n) / 3n;
  const t = k / 3n;
  const residue = Number(k % 3n);
  const q = s.q;
  if (q === 1) {
    if (residue === 0) return L(64n * t + 27n);
    if (residue === 1) return L(64n * t + 37n, 3);
    return L(64n * t + 49n, 6);
  }
  if (residue === 0) return L(64n * t + 17n + 2n * BigInt(q), 1, 5);
  if (residue === 1) return q === 2 ? L(64n * t + 33n, 4, 5) : null;
  const u = Math.floor((2 * q) / 3);
  const rem = (2 * q) % 3;
  if (rem === 0) return L(64n * t + 65n + 8n * BigInt(u));
  if (rem === 1) return L(64n * t + 77n + 8n * BigInt(u));
  return L(64n * t + 59n + 8n * BigInt(u), 3, 2);
}

let index = 0;
let maxV = -1;
let maxRows = [];
let exactHits = [];
let statesScanned = 0;

function record(s, tag) {
  statesScanned++;
  if (s.q !== 0 || s.b !== 0) return;
  let d = (s.a - C) % M;
  if (d < 0n) d += M;
  let v = 0;
  if (d === 0n) v = 108;
  else while (d % 3n === 0n) { d /= 3n; v++; }
  const row = {
    index, tag, v3: v,
    aBits: s.a.toString(2).length,
    aMod81: Number(s.a % 81n)
  };
  if (v > maxV) { maxV = v; maxRows = []; }
  if (v === maxV) maxRows.push(row);
  if (v >= 108) exactHits.push(row);
}

function advance(s, count, tag) {
  for (let i = 0; i < count; i++) {
    record(s, tag);
    const n = nextRegular(s);
    if (n === null) throw new Error(`unexpected DRegular exit in ${tag} at index ${index}`);
    s = n;
    index++;
  }
  return s;
}

function findException(s, tag) {
  while (true) {
    record(s, tag);
    const n = nextRegular(s);
    if (n === null) return s;
    s = n;
    index++;
  }
}

let state = L(9);
const firstSix = [8394, 9422, 12089, 23037, 27291, 31787];
for (let ep = 1; ep <= 6; ep++) {
  state = findException(state, `episode-${ep}`);
  if (index !== firstSix[ep - 1]) throw new Error(`exception index mismatch at ${ep}: ${index}`);
  if (ep < 6) {
    state = secondOfException(state);
    if (state === null) throw new Error(`second exception failed at ${ep}`);
    index += 2;
    record(state, `second-${ep}`);
  }
}

const t6 = (state.a - 7n) / 9n;
if (t6 % 27n !== 23n) throw new Error("episode-6 residue mismatch");
state = L(32768n * (t6 / 27n) + 28577n, 3, 2);
index += 5;
record(state, "reentry-6");
state = advance(state, 34, "to-episode-7");
if (!(state.a % 9n === 4n && state.q === 3 && state.b === 1)) throw new Error("episode-7 mismatch");

const t7 = (state.a - 4n) / 9n;
state = L(64n * t7 + 23n, 1, 5);
index += 2;
record(state, "reentry-7");
state = advance(state, 6046, "to-episode-8");
if (!(state.a % 9n === 1n && state.q === 3 && state.b === 1)) throw new Error("episode-8 mismatch");

const t8 = (state.a - 10n) / 9n;
state = L(64n * t8 + 81n);
index += 2;
record(state, "reentry-8");
state = advance(state, 6090, "to-episode-9");
if (!(state.a % 9n === 4n && state.q === 9 && state.b === 1)) throw new Error("episode-9 mismatch");

const t9 = (state.a - 4n) / 9n;
state = L(64n * t9 + 35n, 1, 5);
index += 2;
record(state, "reentry-9");
state = advance(state, 41, "to-episode-10");
if (!(state.a % 9n === 4n && state.q === 6 && state.b === 1)) throw new Error("episode-10 mismatch");

const t10 = (state.a - 4n) / 9n;
state = L(64n * t10 + 29n, 1, 5);
index += 2;
record(state, "reentry-10");
state = advance(state, 1708, "to-episode-11");
if (!(state.a % 9n === 7n && state.q === 6 && state.b === 1)) throw new Error("episode-11 mismatch");

const t11 = (state.a - 7n) / 9n;
if (t11 % 27n !== 4n) throw new Error("episode-11 packet residue mismatch");
state = L(32768n * (t11 / 27n) + 5493n);
index += 5;
record(state, "reentry-11");
state = advance(state, 1759, "to-episode-12");
if (!(state.a % 9n === 1n && state.q === 7 && state.b === 1)) throw new Error("episode-12 mismatch");

const t12 = (state.a - 10n) / 9n;
state = L(64n * t12 + 91n, 3, 2);
index += 2;
record(state, "reentry-12");
state = advance(state, 3679, "to-episode-13");
if (!(state.a % 9n === 4n && state.q === 6 && state.b === 1)) throw new Error("episode-13 mismatch");

const t13 = (state.a - 4n) / 9n;
state = L(64n * t13 + 29n, 1, 5);
index += 2;
record(state, "reentry-13");
if (index !== 51166) throw new Error(`pre-episode-14 index mismatch: ${index}`);

const episodes14to17 = [
  [5169, 4, 5, 3, 79720, 31],
  [6821, 4, 8, 14, 89375, 49],
  [2077, 4, 5, 26, 92317, 76],
  [2656, 7, 7, 6, 96078, 61]
];
for (let ep = 14; ep <= 17; ep++) {
  const [steps, residue, q, tmod, bits, mod81] = episodes14to17[ep - 14];
  state = advance(state, steps, `episode-${ep}`);
  const offset = residue === 7 ? 7n : 4n;
  const t = (state.a - offset) / 9n;
  if (!(Number(state.a % 9n) === residue &&
        state.q === q && Number(t % 27n) === tmod &&
        state.a.toString(2).length === bits &&
        Number(state.a % 81n) === mod81)) {
    throw new Error(`episode-${ep} fingerprint mismatch`);
  }
  if (ep < 17) {
    state = secondOfException(state);
    if (state === null) throw new Error(`second exception failed at ${ep}`);
    index += 2;
    record(state, `second-${ep}`);
  }
}

const t17 = (state.a - 7n) / 9n;
if (t17 % 27n !== 6n) throw new Error("episode-17 packet residue mismatch");
const u17 = t17 / 3n;
state = L(8n * (64n * u17 + 10n) + 39n, 3, 2);
index += 3;
record(state, "reentry-17");

const episodes18to20 = [
  [2902, 4, 3, 22, 100189, 40],
  [9780, 1, 9, 12, 114030, 37],
  [2040, 7, 5, 4, 116920, 43]
];
for (let j = 0; j < 3; j++) {
  const ep = 18 + j;
  const [steps, residue, q, tmod, bits, mod81] = episodes18to20[j];
  state = advance(state, steps, `episode-${ep}`);
  const offset = residue === 7 ? 7n : residue === 4 ? 4n : 10n;
  const t = (state.a - offset) / 9n;
  if (!(Number(state.a % 9n) === residue &&
        state.q === q && Number(t % 27n) === tmod &&
        state.a.toString(2).length === bits &&
        Number(state.a % 81n) === mod81)) {
    throw new Error(`episode-${ep} fingerprint mismatch`);
  }
  if (ep === 18) {
    state = L(64n * t + 23n, 1, 5);
    index += 2;
    record(state, "reentry-18");
  }
  if (ep === 19) {
    state = L(64n * t + 113n, 0, 0);
    index += 2;
    record(state, "reentry-19");
  }
}
record(state, "episode-20-endpoint");

console.log(JSON.stringify({
  finalIndex: index,
  statesScanned,
  final: { q: state.q, b: state.b, aBits: state.a.toString(2).length },
  maxV3: maxV,
  maxRows,
  exactHits
}, null, 2));
