// Exact BigInt witness: a locally legal delta=1, Is=20 prepared-state
// suffix reaches the wall, but its high-depth parent is not root-reachable.
// No floating-point arithmetic or external packages are used.

function assert(condition, message) {
  if (!condition) throw new Error(message);
}
function mod(a, m) { return ((a % m) + m) % m; }
function v2(x) {
  assert(x > 0n, "v2 requires a positive integer");
  let e = 0;
  while ((x & 1n) === 0n) { x >>= 1n; e++; }
  return e;
}
function isParent(s) {
  return s.b >= 8n && s.b % 4n === 0n && s.d % 2n === 1n;
}

// One inverseAt edge of depth t, checked from the exact source power and
// mass equations. The returned child has cost m+t+1.
function inverseEdge(parent, t, label) {
  assert(isParent(parent), label + ": invalid parent guard");
  const X = parent.d + parent.b / 2n + 3n;
  const den = 2n ** BigInt(t);
  assert(X % den === 0n, label + ": power equation not integral");
  const cPlus3 = X / den;
  assert(cPlus3 % 2n === 0n, label + ": c is not odd");
  const c = cPlus3 - 3n;
  const twoK = parent.b + parent.d - c - 2n * BigInt(t) - 2n;
  assert(twoK % 2n === 0n, label + ": mass equation not integral");
  const k = twoK / 2n;
  assert(c >= 1n, label + ": c<1");
  assert(k >= 2n, label + ": k<2");
  const child = {
    b: 2n * k - 4n,
    d: c + 4n,
    m: parent.m + BigInt(t) + 1n
  };
  return { child, k, c, X };
}

function lowStep(I, B, P, depth) {
  if (depth === 0) {
    const numerator = I - 588n * P + 84n * B - 232n;
    assert(numerator % 2n === 0n, "depth-0 LowStep not integral");
    return { I: numerator / 2n, B: B + 1n };
  }
  if (depth === 1) {
    const numerator = I - 392n * P + 56n * B - 136n;
    assert(numerator % 4n === 0n, "depth-1 LowStep not integral");
    return { I: numerator / 4n, B: B + 2n };
  }
  assert(I % 8n === 0n, "depth-2 LowStep not integral");
  return { I: I / 8n, B: B + 3n };
}

const n = 182n;
const P = 2n ** n;
const delta = 1n;
const s = (n + delta) / 3n;
assert((n + delta) % 3n === 0n && s === 61n, "wrong restart count");

const uNumerator = 21n * P - 32n;
assert(uNumerator % 106n === 0n, "u is not integral");
const u = uNumerator / 106n;
const M = 14n * u - n - delta - 1n;
const defectNumerator = 58n * P + 6n - 14n * M;
assert(defectNumerator % 49n === 0n, "D is not integral");
const D = defectNumerator / 49n;
const c = D - 3n;
const energyNumerator = 40n * P + 42n * D - 76n;
assert(energyNumerator % 14n === 0n, "k is not integral");
const k = energyNumerator / 14n;
const t = 4n;
const qNumerator = 40n * P - 76n;
assert(qNumerator % 7n === 0n, "q formula is not integral");
const q = (7n - 2n ** t) * D + qNumerator / 7n + 2n * t + 2n;
const d = 2n ** t * D - q - 3n;
const mParent = M - n - t - 1n;
assert(mParent >= 0n, "negative high-depth parent cost");

assert(M === mParent + n + t + 1n, "restart-cost identity");
assert(M + 3n > P, "record the prepared suffix excess over the proposed extra bound");
assert(49n * D + 14n * M === 58n * P + 6n, "delta=1 defect");
assert(14n * k === 40n * P + 42n * c + 50n, "high-depth energy identity");

const highParent = { b: 2n * q, d, m: mParent };
const high = inverseEdge(highParent, Number(t), "high-depth t=4");
assert(high.k === k && high.c === c, "high-depth inverse parameters");
assert(2n ** t * D === d + q + 3n, "high-depth power equation");
assert(2n * k + c + 2n * t + 2n === highParent.b + highParent.d,
  "high-depth mass equation");

let state = high.child;
const depthTwoParameters = [];
for (let i = 0; i < Number(s); i++) {
  const edge = inverseEdge(state, 2, "depth-two edge " + i);
  depthTwoParameters.push({ k: edge.k, c: edge.c });
  state = edge.child;
}

const expectedFirstShallow = {
  b: 12n * P - 24n * u - 12n,
  d: 2n * P - 4n * u + 1n,
  m: M - n + 3n * s
};
assert(state.b === expectedFirstShallow.b, "first-shallow b coordinate");
assert(state.d === expectedFirstShallow.d, "first-shallow d coordinate");
assert(state.m === expectedFirstShallow.m, "first-shallow cost");
const T = M + 6n + 3n * s;
assert(T === 14n * u + 5n, "A-branch offset");
assert(state.b + 18n === 6n * state.d, "A-branch b/d equation");
assert(7n * state.d + 2n * T === 14n * P + 17n, "A-branch mass equation");

// The scalar LowTrace is Is=20 at this first-shallow parent, then three
// depth-zero steps reach I+112B=384.
assert(40n * P === 20n * 8n ** s, "energy after 61 depth-two steps");
let low = { I: 40n * P, B: M + 6n };
for (let i = 0; i < Number(s); i++) low = lowStep(low.I, low.B, P, 2);
assert(low.I === 20n && low.B === T, "first-shallow LowTrace state");
for (let i = 0; i < 3; i++) low = lowStep(low.I, low.B, P, 0);
assert(low.I + 112n * low.B === 384n, "scalar wall equation");

const shallowParameters = [];
for (let i = 0; i < 3; i++) {
  const edge = inverseEdge(state, 0, "terminal depth-zero edge " + i);
  shallowParameters.push({ k: edge.k, c: edge.c });
  state = edge.child;
}
assert(state.b + 4n * state.m + 4n * n + 20n === 12n * P,
  "terminal source wall equation");

// Exhaust the exact root cone for n=182. Every possible depth is tested:
// t ranges from 0 through v2(X)-1, exactly the range for c+3 even.
function rootChildren(parent) {
  const X = parent.d + parent.b / 2n + 3n;
  const out = [];
  for (let depth = 0; depth < v2(X); depth++) {
    try {
      const edge = inverseEdge(parent, depth, "root-cone candidate");
      if (isParent(edge.child)) out.push({ depth, child: edge.child });
    } catch (_) {
      // This depth is not a legal inverseAt edge.
    }
  }
  return out;
}
let root = { b: 14n * P - 2n * n - 16n, d: 3n, m: 0n };
assert(isParent(root), "root parent guard");
const rootWord = [];
while (true) {
  const next = rootChildren(root);
  assert(next.length <= 1, "unexpected root branching");
  if (next.length === 0) break;
  rootWord.push(next[0].depth);
  root = next[0].child;
  assert(rootWord.length < 10, "unexpectedly long root cone");
}
assert(rootWord.length === 2 && rootWord[0] === 0 && rootWord[1] === 0,
  "root cone is not the expected 0,0 chain");

console.log(JSON.stringify({
  n: String(n),
  P_bits: P.toString(2).length,
  delta: String(delta),
  u: String(u),
  s_depth_two: String(s),
  M: String(M),
  exceeds_proposed_extra_bound: M + 3n > P,
  D: String(D),
  high_depth: String(t),
  high_parent: { b: String(highParent.b), d: String(highParent.d), m: String(highParent.m) },
  restart_child: { b: String(high.child.b), d: String(high.child.d), m: String(high.child.m) },
  first_shallow_parent: {
    b: String(expectedFirstShallow.b), d: String(expectedFirstShallow.d),
    m: String(expectedFirstShallow.m), T: String(T)
  },
  depth_two_edges_checked: depthTwoParameters.length,
  terminal_depths: [0, 0, 0],
  terminal_edge_parameters: shallowParameters.map(x => ({ k: String(x.k), c: String(x.c) })),
  wall: { b: String(state.b), d: String(state.d), m: String(state.m) },
  root_cone_depth_word: rootWord,
  root_cone_dead_state: { b: String(root.b), d: String(root.d), m: String(root.m) }
}, null, 2));
