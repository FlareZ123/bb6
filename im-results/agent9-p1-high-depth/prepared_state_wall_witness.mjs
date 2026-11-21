// Exact BigInt checker for the prepared-state wall witness at n = 808.
// Run with Node.js; no dependencies.
function assert(ok, message) {
  if (!ok) throw new Error(message);
}
function edge(state, depth) {
  assert(state.b >= 8n && state.b % 4n === 0n && state.d >= 1n && state.d % 2n === 1n,
    "source parent guards failed");
  const x = state.d + state.b / 2n + 3n;
  const denominator = 1n << depth;
  assert(x % denominator === 0n, "source power division failed");
  const c = x / denominator - 3n;
  const kNumerator = state.b + state.d - c - 2n * depth - 2n;
  assert(c % 2n === 1n && kNumerator % 2n === 0n, "source c/k parity failed");
  const k = kNumerator / 2n;
  assert(k >= 2n, "source k lower bound failed");
  return { b: 2n * k - 4n, d: c + 4n, m: state.m + depth + 1n };
}

const n = 808n;
const P = 1n << n;
const uNumerator = 34n * P - 1272n;
const uDenominator = 2116n;
assert(uNumerator % uDenominator === 0n, "u is not integral");
const u = uNumerator / uDenominator;
const DNumerator = 18n * P - 196n * u + 14n * n + 48n;
assert(DNumerator % 49n === 0n, "D is not integral");
const D = DNumerator / 49n;
assert(D >= 4n && D % 2n === 0n, "D positivity/parity failed");

const M = 14n * u - n - 3n;
const m0 = M - n;
const t = 5n;
const mp = m0 - t - 1n;
assert(mp >= 0n, "prepared parent mass is negative");
const X = (1n << t) * D;
const q = 14n * P - X - 2n * mp - 2n * n - 10n;
const dp = X - q - 3n;
const cp = D - 3n;
const kpNumerator = q + X - cp - 2n * t - 5n;
assert(kpNumerator % 2n === 0n, "high-edge k is not integral");
const kp = kpNumerator / 2n;
const parent = { b: 2n * q, d: dp, m: mp };
const restart = { b: 2n * kp - 4n, d: cp + 4n, m: m0 };

assert(parent.b >= 8n && parent.b % 4n === 0n && parent.d >= 1n && parent.d % 2n === 1n,
  "prepared parent guards failed");
assert(cp % 2n === 1n && kp >= 2n, "high-edge parameters failed");
assert(X === dp + q + 3n, "high-edge power equation failed");
assert(2n * kp + cp + 2n * t + 2n === parent.b + parent.d, "high-edge mass equation failed");
assert(parent.b + parent.d + 2n * parent.m + 2n * n + 13n === 14n * P,
  "prepared parent mass invariant failed");
assert(restart.b >= 8n && restart.b % 4n === 0n && restart.d % 2n === 1n,
  "restart child guards failed");
assert(restart.b + restart.d + 2n * restart.m + 2n * n + 13n === 14n * P,
  "restart child mass invariant failed");

// The actual n=808 root cone has height at most one.
// S0 = 7P - n - 2 is 2 mod 4, forcing the only root edge to have depth 0.
const root = { b: 14n * P - 2n * n - 16n, d: 3n, m: 0n };
const rootS = root.d + root.b / 2n + 3n;
assert(rootS % 4n === 2n, "root power is not 2 mod 4");
const rootC = rootS - 3n;
const rootKNumerator = root.b + root.d - rootC - 2n;
assert(rootKNumerator % 2n === 0n, "root child k is not integral");
const rootK = rootKNumerator / 2n;
assert(rootK >= 2n, "root child k below 2");
const rootChildB = 2n * rootK - 4n;
assert(rootChildB % 4n === 2n, "root child left counter is not 2 mod 4");
assert(mp > 1n, "prepared parent unexpectedly has cost at most one");

// The 270-edge depth-two prefix.
let state = restart;
const s = 270;
for (let i = 0; i < s; i++) state = edge(state, 2n);
const bShallow = 12n * P - 24n * u - 12n;
const dShallow = 2n * P - 4n * u + 1n;
const mShallow = M + 2n;
assert(state.b === bShallow && state.d === dShallow && state.m === mShallow,
  "depth-two prefix endpoint mismatch");

// First shallow edge, of depth zero.
state = edge(state, 0n);
assert(state.b === 6n * P - 12n * u - 12n
  && state.d === 8n * P - 16n * u - 1n
  && state.m === M + 3n, "first shallow endpoint mismatch");

// The remaining low-depth word (0, 1, 2).
for (const depth of [0n, 1n, 2n]) state = edge(state, depth);
assert(state.b + 4n * state.m + 4n * n + 20n === 12n * P,
  "shifted wall equation failed");
assert(state.m - parent.m === 823n, "total inverse-cost increment mismatch");

console.log(JSON.stringify({
  n: String(n),
  uDigits: String(u).length,
  DDigits: String(D).length,
  depthTwoPrefixEdges: s,
  firstShallowDepth: 0,
  finalDepthWord: [0, 1, 2],
  totalSourceEdges: 275,
  totalInverseCost: 823,
  wallReached: true,
  originalRootPrefixProved: false,
  originalRootConeHeightAtMostOne: true
}, null, 2));
