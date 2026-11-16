// Exploratory search only; not a proof of non-reachability.
// Direct transcription of the section map in im-results/agent46-c-jump/FastSectionDef.lean.
// Run with Node.js: node U5Q0OrbitSearch.js [steps]

function bounce(K, C) {
  let k = K, c = C;
  for (;;) {
    if (c < 4n) return null;
    if (k % 2n === 1n) {
      if (c <= 2n * k + 6n) return [2n * k + 6n - c, c];
      const old = k;
      c -= 2n * old + 3n;
      k = 2n * old + 3n;
    } else {
      if (c === 4n) return [2n * k + 2n, 3n];
      if (c === 5n) return null;
      if (c <= 2n * k + 8n) return [2n * k + 8n - c, c - 1n];
      const old = k;
      c -= 2n * old + 5n;
      k = 2n * old + 4n;
    }
  }
}

function secNext(a, k) {
  if (a === 0n) {
    if (k === 0n) return null;
    if (k === 1n) return [0n, 4n];
    return bounce(1n, 2n * k + 1n);
  }
  if (a === 1n) {
    if (k === 0n) return [5n, 1n];
    if (k === 1n) return [2n, 3n];
    if (k === 2n) return [2n, 5n];
    if (k === 3n) return [0n, 7n];
    return bounce(4n, 2n * k - 3n);
  }
  if (k === 0n) return [a - 2n, 2n];
  if (2n * k <= a) return [a - 2n * k, 2n * k + 2n];
  return bounce(a - 1n, 2n * k - a + 3n);
}

const steps = Number(process.argv[2] || 5_000_000);
const qPowers = Array.from({ length: 20 }, (_, q) => 4n ** BigInt(q));
const targetTResidues = new Set([81, 123, 39]);
const oddModuli = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43];
const residueSets = new Map(oddModuli.map(m => [m, new Set()]));

let a = 5n, k = 1n;
let candidateCount = 0, exactFanHits = [], q0Hits = [];
let minAbsLinearResidual = null, minResidualState = null;
let firstMillion = Math.min(steps, 1_000_000);

for (let i = 0; i < steps; i++) {
  if (i < firstMillion) {
    for (const m of oddModuli) {
      residueSets.get(m).add(`${a % BigInt(m)},${k % BigInt(m)}`);
    }
  }

  const M = a + 2n * k + 10n;
  const L = 85n * a - 86n * k;
  const absResidual = L >= 46n ? L - 46n : 46n - L;
  if (minAbsLinearResidual === null || absResidual < minAbsLinearResidual) {
    minAbsLinearResidual = absResidual;
    minResidualState = { step: i, a: a.toString(), k: k.toString(), L: L.toString() };
  }
  if (L === 46n && q0Hits.length < 20) {
    q0Hits.push({ step: i, a: a.toString(), k: k.toString(), M: M.toString() });
  }

  for (let q = 0; q < qPowers.length; q++) {
    const v = M + 6n * BigInt(q);
    if (v % 128n !== 0n) continue;
    const t = v / 128n;
    if (!targetTResidues.has(Number(t % 168n))) continue;
    candidateCount++;
    if (43n * t - 1n === qPowers[q] * (a + 2n)) {
      exactFanHits.push({ step: i, q, t: t.toString(), a: a.toString(), k: k.toString() });
    }
  }

  const next = secNext(a, k);
  if (next === null) break;
  [a, k] = next;
}

const residueCoverage = Object.fromEntries(
  oddModuli.map(m => [m, residueSets.get(m).size])
);
console.log(JSON.stringify({
  steps,
  candidateCount,
  exactFanHits,
  q0Hits,
  minAbsLinearResidual: minAbsLinearResidual?.toString(),
  minResidualState,
  firstMillionResidueCoverage: residueCoverage,
  finalState: { a: a.toString(), k: k.toString() }
}, null, 2));
