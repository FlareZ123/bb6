import { readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

// Compare every modeled authentic-root DRegular section through episode 20
// with the canonical A-sections on the external 107-call halting path.
// This is an exact finite arithmetic screen, not an all-time root theorem.

const HERE = dirname(fileURLToPath(import.meta.url));
const trace = JSON.parse(readFileSync(
  join(HERE, '..', 'agent4-cryptid-macro-replay', 'macro_trace.json'), 'utf8'));
const C = BigInt(trace.initial.n);
const MOD10 = 3n ** 10n;
const TARGET_CLASSES = new Set([
  '0,0', '1,0', '1,1', '3,1', '4,1', '3,2', '4,0'
]);

function L(a, q = 0, b = 0) {
  return { a: BigInt(a), q, b };
}

function parseRegularSuffix(input) {
  const r = input.slice();
  while (r.length && r[r.length - 1] === 0) r.pop();
  for (let q = 0; q <= Math.floor(r.length / 2); q++) {
    const prefix = [];
    for (let i = 0; i < q; i++) prefix.push(0, 1);
    if (prefix.every((x, i) => r[i] === x) &&
        r.length >= prefix.length &&
        r.slice(prefix.length).every(x => x === 1) &&
        (q > 0 || r.length === 0)) {
      return [q, r.length - prefix.length];
    }
  }
  return null;
}

function valuation3(delta, cap) {
  let d = delta < 0n ? -delta : delta;
  if (d === 0n) return cap;
  let v = 0;
  while (v < cap && d % 3n === 0n) {
    d /= 3n;
    v++;
  }
  return v;
}

const externalStates = [
  { j: 0, n: C, suffix: trace.initial.suffix },
  ...trace.steps.map((step, i) => ({
    j: i + 1, n: BigInt(step.output_n), suffix: step.output_suffix
  }))
].map(s => ({ ...s, cls: parseRegularSuffix(s.suffix) }))
 .filter(s => s.cls !== null);

const externalByClass = new Map();
const prefixStats = new Map();
for (const e of externalStates) {
  const key = e.cls.join(',');
  if (!externalByClass.has(key)) externalByClass.set(key, []);
  externalByClass.get(key).push({
    ...e,
    coefficient: (3n ** BigInt(108 - e.j)) * (8n ** BigInt(e.j))
  });
  prefixStats.set(e.j, {
    j: e.j, q: e.cls[0], b: e.cls[1],
    count: 0, maxV3: -1, maxRows: [], exactLifts: 0
  });
}

const classStats = new Map();
for (const key of TARGET_CLASSES) {
  classStats.set(key, { class: key, count: 0, maxV3: -1, maxRows: [], lowModHits: 0 });
}

let index = 0;
let statesScanned = 0;

function record(s, tag) {
  statesScanned++;
  const key = s.q + ',' + s.b;

  const cs = classStats.get(key);
  if (cs) {
    const v = valuation3(s.a - C, 108);
    const row = { index, tag, v3: v, aBits: s.a.toString(2).length };
    cs.count++;
    if (v > cs.maxV3) {
      cs.maxV3 = v;
      cs.maxRows = [row];
    } else if (v === cs.maxV3) {
      cs.maxRows.push(row);
    }
    if (s.a % MOD10 === C % MOD10) cs.lowModHits++;
  }

  for (const e of externalByClass.get(key) || []) {
    const delta = s.a - e.n;
    const cap = 108 - e.j;
    const v = valuation3(delta, cap);
    const exactLift = delta >= 0n && delta % e.coefficient === 0n;
    const ps = prefixStats.get(e.j);
    const row = {
      index, tag, v3: v, deltaNonnegative: delta >= 0n,
      exactLift, aBits: s.a.toString(2).length
    };
    ps.count++;
    if (v > ps.maxV3) {
      ps.maxV3 = v;
      ps.maxRows = [row];
    } else if (v === ps.maxV3) {
      ps.maxRows.push(row);
    }
    if (exactLift) ps.exactLifts++;
  }
}

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

function advance(s, count, tag) {
  for (let i = 0; i < count; i++) {
    record(s, tag);
    const next = nextRegular(s);
    if (next === null) throw new Error('unexpected DRegular exit in ' + tag);
    s = next;
    index++;
  }
  return s;
}

function findException(s, tag) {
  while (true) {
    record(s, tag);
    const next = nextRegular(s);
    if (next === null) return s;
    s = next;
    index++;
  }
}

let state = L(9);
const firstSix = [8394, 9422, 12089, 23037, 27291, 31787];
for (let ep = 1; ep <= 6; ep++) {
  state = findException(state, 'episode-' + ep);
  if (index !== firstSix[ep - 1]) throw new Error('exception index mismatch at ' + ep);
  if (ep < 6) {
    state = secondOfException(state);
    if (state === null) throw new Error('second exception failed at ' + ep);
    index += 2;
    record(state, 'second-' + ep);
  }
}

const t6 = (state.a - 7n) / 9n;
if (t6 % 27n !== 23n) throw new Error('episode-6 residue mismatch');
state = L(32768n * ((t6 - 23n) / 27n) + 28577n, 3, 2);
index += 5;
record(state, 'reentry-6');
const externalMacro2 = externalStates.find(e => e.j === 2);
if (!externalMacro2) throw new Error('external macro-2 state missing');
const macro2Delta = state.a - externalMacro2.n;
const macro2Coefficient = (3n ** 106n) * (8n ** 2n);
const rootReentryComparison = {
  rootSectionIndex: index,
  suffix: '01010111',
  rootParameterMod3: Number(state.a % 3n),
  externalMacro2ParameterMod3: Number(externalMacro2.n % 3n),
  v3Difference: valuation3(macro2Delta, 106),
  exactMacro2CylinderLift: macro2Delta >= 0n && macro2Delta % macro2Coefficient === 0n
};
if (rootReentryComparison.v3Difference !== 0 || rootReentryComparison.rootParameterMod3 === rootReentryComparison.externalMacro2ParameterMod3) {
  throw new Error('unexpected q3,b2 reentry relation to external macro 2');
}

state = advance(state, 34, 'to-episode-7');
if (!(state.a % 9n === 4n && state.q === 3 && state.b === 1)) throw new Error('episode-7 mismatch');
let t = (state.a - 4n) / 9n;
state = L(64n * t + 23n, 1, 5);
index += 2;
record(state, 'reentry-7');

state = advance(state, 6046, 'to-episode-8');
if (!(state.a % 9n === 1n && state.q === 3 && state.b === 1)) throw new Error('episode-8 mismatch');
t = (state.a - 10n) / 9n;
state = L(64n * t + 81n);
index += 2;
record(state, 'reentry-8');

state = advance(state, 6090, 'to-episode-9');
if (!(state.a % 9n === 4n && state.q === 9 && state.b === 1)) throw new Error('episode-9 mismatch');
t = (state.a - 4n) / 9n;
state = L(64n * t + 35n, 1, 5);
index += 2;
record(state, 'reentry-9');

state = advance(state, 41, 'to-episode-10');
if (!(state.a % 9n === 4n && state.q === 6 && state.b === 1)) throw new Error('episode-10 mismatch');
t = (state.a - 4n) / 9n;
state = L(64n * t + 29n, 1, 5);
index += 2;
record(state, 'reentry-10');

state = advance(state, 1708, 'to-episode-11');
if (!(state.a % 9n === 7n && state.q === 6 && state.b === 1)) throw new Error('episode-11 mismatch');
t = (state.a - 7n) / 9n;
if (t % 27n !== 4n) throw new Error('episode-11 packet residue mismatch');
state = L(32768n * (t / 27n) + 5493n);
index += 5;
record(state, 'reentry-11');

state = advance(state, 1759, 'to-episode-12');
if (!(state.a % 9n === 1n && state.q === 7 && state.b === 1)) throw new Error('episode-12 mismatch');
t = (state.a - 10n) / 9n;
state = L(64n * t + 91n, 3, 2);
index += 2;
record(state, 'reentry-12');

state = advance(state, 3679, 'to-episode-13');
if (!(state.a % 9n === 4n && state.q === 6 && state.b === 1)) throw new Error('episode-13 mismatch');
t = (state.a - 4n) / 9n;
state = L(64n * t + 29n, 1, 5);
index += 2;
record(state, 'reentry-13');
if (index !== 51166) throw new Error('pre-episode-14 index mismatch');

const episodes14to17 = [
  [5169, 4, 5, 3, 79720, 31],
  [6821, 4, 8, 14, 89375, 49],
  [2077, 4, 5, 26, 92317, 76],
  [2656, 7, 7, 6, 96078, 61]
];
for (let ep = 14; ep <= 17; ep++) {
  const [steps, residue, q, tmod, bits, mod81] = episodes14to17[ep - 14];
  state = advance(state, steps, 'episode-' + ep);
  const offset = residue === 7 ? 7n : 4n;
  t = (state.a - offset) / 9n;
  if (!(Number(state.a % 9n) === residue && state.q === q &&
        Number(t % 27n) === tmod && state.a.toString(2).length === bits &&
        Number(state.a % 81n) === mod81)) {
    throw new Error('episode-' + ep + ' fingerprint mismatch');
  }
  if (ep < 17) {
    state = secondOfException(state);
    if (state === null) throw new Error('second exception failed at ' + ep);
    index += 2;
    record(state, 'second-' + ep);
  }
}

t = (state.a - 7n) / 9n;
if (t % 27n !== 6n) throw new Error('episode-17 packet residue mismatch');
const u17 = t / 3n;
state = L(8n * (64n * u17 + 10n) + 39n, 3, 2);
index += 3;
record(state, 'reentry-17');

const episodes18to20 = [
  [2902, 4, 3, 22, 100189, 40],
  [9780, 1, 9, 12, 114030, 37],
  [2040, 7, 5, 4, 116920, 43]
];
for (let j = 0; j < 3; j++) {
  const ep = 18 + j;
  const [steps, residue, q, tmod, bits, mod81] = episodes18to20[j];
  state = advance(state, steps, 'episode-' + ep);
  const offset = residue === 7 ? 7n : residue === 4 ? 4n : 10n;
  t = (state.a - offset) / 9n;
  if (!(Number(state.a % 9n) === residue && state.q === q &&
        Number(t % 27n) === tmod && state.a.toString(2).length === bits &&
        Number(state.a % 81n) === mod81)) {
    throw new Error('episode-' + ep + ' fingerprint mismatch');
  }
  if (ep === 18) {
    state = L(64n * t + 23n, 1, 5);
    index += 2;
    record(state, 'reentry-18');
  }
  if (ep === 19) {
    state = L(64n * t + 113n, 0, 0);
    index += 2;
    record(state, 'reentry-19');
  }
}
record(state, 'episode-20-endpoint');
if (index !== 82624) throw new Error('final section index mismatch');

const candidateSuffixes = [...classStats.values()].sort((a, b) => b.maxV3 - a.maxV3);
const prefixComparisons = [...prefixStats.values()].sort((a, b) => a.j - b.j);
const exactLifts = prefixComparisons.filter(x => x.exactLifts > 0);

console.log(JSON.stringify({
  scope: 'DRegular sections and explicit reentry endpoints only; through episode 20',
  finalSectionIndex: index,
  statesScanned,
  cylinderBaseMod3Pow10: Number(C % MOD10),
  candidateSuffixes,
  rootReentryComparison,
  externalPrefixComparisons: prefixComparisons,
  exactPrefixCylinderLifts: exactLifts
}, null, 2));
