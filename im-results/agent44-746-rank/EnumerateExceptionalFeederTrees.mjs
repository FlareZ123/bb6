#!/usr/bin/env node
/**
 * Exact finite inverse-tree census for the distinguished t=1 odd feeder of
 * #746's fatal reset heights. This is a diagnostic, not an all-index proof.
 *
 * Source relation: im-results/agent10-cascade/FirstInverseComplete.lean
 *
 * ResetParent(h,u) has two exact branches:
 *   even: u in [6*2^m-1, 8*2^m-3], 2*u = 8*2^m + h + m;
 *   odd:  d odd, q=2^t*d in [6*2^m+1,8*2^m-1],
 *         2*u+5=3^(t+1)*d, 2*q=8*2^m+h+m+5.
 *
 * Every calculation below uses BigInt. The unique possible dyadic scale is
 * m=floor(log2(q))-2 (bitLength(q)-3), so no floating-point logarithms or
 * bounded search over m are used. The odd-valuation loop stops exactly at
 * v_3(2*u+5), so every possible t is considered.
 *
 * Run: node EnumerateExceptionalFeederTrees.mjs
 */
const RESIDUES = [113, 400, 526, 599, 886, 887, 1085, 1372];
const SAMPLE_PERIODS = [1458, 13122];
const SAMPLE_MULTIPLIERS = [0, 1, 2, 10];
const NINE_LIFT_BASE_PERIOD = 1458;
const NINE_LIFT_SAMPLE_PERIOD = 13122;
const NINE_LIFT_OFFSETS = Array.from({ length: 9 }, (_, k) => k);

const pow2 = (k) => 1n << BigInt(k);
const bitLength = (n) => n <= 0n ? 0 : n.toString(2).length;

function assert(condition, message) {
  if (!condition) throw new Error(message);
}

function valuation3(value) {
  let n = value;
  let v = 0;
  while (n !== 0n && n % 3n === 0n) {
    n /= 3n;
    v += 1;
  }
  return v;
}

function resetParents(u, n) {
  const out = [];

  // The even band has at most one scale, determined exactly by bit length.
  const evenM = bitLength(u) - 3;
  if (evenM >= 0) {
    const p = pow2(evenM);
    if (6n * p - 1n <= u && u <= 8n * p - 3n) {
      out.push({
        kind: "E",
        t: null,
        scaleOffset: n - evenM,
        height: 2n * u - 8n * p - BigInt(evenM),
      });
    }
  }

  // Enumerate all t with 3^(t+1) | (2*u+5), and no others.
  const numerator = 2n * u + 5n;
  let remaining = numerator;
  let valuation = 0;
  while (remaining % 3n === 0n) {
    remaining /= 3n;
    valuation += 1;
  }

  let power3 = 3n;
  let power2 = 1n;
  for (let t = 0; t < valuation; t += 1) {
    const d = numerator / power3;
    if (d % 2n === 1n) {
      const q = power2 * d;
      const oddM = bitLength(q) - 3;
      if (oddM >= 0) {
        const p = pow2(oddM);
        if (6n * p + 1n <= q && q <= 8n * p - 1n) {
          out.push({
            kind: "O",
            t,
            scaleOffset: n - oddM,
            height: 2n * q - 8n * p - BigInt(oddM) - 5n,
          });
        }
      }
    }
    power3 *= 3n;
    power2 *= 2n;
  }

  return out;
}

function buildTree(n) {
  assert(Number.isSafeInteger(n) && n >= 76, "n must be a safe integer >= 76");
  const N = BigInt(n);
  const p = pow2(n - 2);
  const fatal = 4n * pow2(n) - N - 4n;
  const numerator = 2n * fatal + 5n;
  assert(numerator % 9n === 0n, "fatal numerator is not divisible by 9");
  const d = numerator / 9n;
  const feeder = 4n * d - 8n * p - N - 3n;

  // Check the defining t=1 parent edge fatal <- feeder.
  const q = 2n * d;
  assert(6n * p + 1n <= q && q <= 8n * p - 1n,
    "distinguished t=1 feeder is outside its odd band");
  assert(2n * q === 8n * p + feeder + N + 3n,
    "distinguished t=1 ResetParent equation failed");

  const nodes = [{ height: feeder, depth: 0, incoming: null }];
  const ids = new Map([[feeder.toString(), 0]]);
  const edges = [];

  for (let i = 0; i < nodes.length; i += 1) {
    const current = nodes[i];
    for (const parent of resetParents(current.height, n)) {
      const key = parent.height.toString();
      let j = ids.get(key);
      if (j === undefined) {
        j = nodes.length;
        ids.set(key, j);
        nodes.push({
          height: parent.height,
          depth: current.depth + 1,
          incoming: { kind: parent.kind, t: parent.t, scaleOffset: parent.scaleOffset },
        });
      }
      edges.push({
        from: i,
        to: j,
        kind: parent.kind,
        t: parent.t,
        scaleOffset: parent.scaleOffset,
      });
    }
  }

  const outgoing = new Set(edges.map((edge) => edge.from));
  const leaves = nodes
    .map((node, id) => ({ id, depth: node.depth, height: node.height }))
    .filter((node) => !outgoing.has(node.id));

  return {
    n,
    feeder,
    nodes,
    edges,
    leaves,
    maxDepth: Math.max(...nodes.map((node) => node.depth)),
    initialOddValuation: valuation3(2n * feeder + 5n),
  };
}

function topologySignature(tree) {
  return tree.edges
    .map((edge) => `${edge.from}>${edge.to}:${edge.kind}${edge.t ?? ""}@-${edge.scaleOffset}`)
    .join("|");
}

const report = RESIDUES.map((r) => {
  const finiteSamples = SAMPLE_PERIODS.map((period) => {
    const samples = SAMPLE_MULTIPLIERS.map((T) => {
      const tree = buildTree(r + period * T);
      return {
        T,
        nodes: tree.nodes.length,
        edges: tree.edges.length,
        leaves: tree.leaves.length,
        maxDepth: tree.maxDepth,
        initialOddValuation: tree.initialOddValuation,
        signature: topologySignature(tree),
      };
    });
    return {
      period,
      samples: samples.map(({ signature, ...summary }) => summary),
      sameSampledTopology: samples.every((sample) => sample.signature === samples[0].signature),
    };
  });
  // A fixed r mod 1458 has nine distinct lifts modulo 13122. Sample all of
  // them separately; n=r+13122*T alone sees only lift k=0.
  const nineLiftDiagnostics = NINE_LIFT_OFFSETS.map((k) => {
    const baseN = r + NINE_LIFT_BASE_PERIOD * k;
    const samples = SAMPLE_MULTIPLIERS.map((T) => {
      const tree = buildTree(baseN + NINE_LIFT_SAMPLE_PERIOD * T);
      return {
        T,
        nodes: tree.nodes.length,
        edges: tree.edges.length,
        leaves: tree.leaves.length,
        maxDepth: tree.maxDepth,
        initialOddValuation: tree.initialOddValuation,
        signature: topologySignature(tree),
      };
    });
    return {
      lift: k,
      baseN,
      samples: samples.map(({ signature, ...summary }) => summary),
      sameSampledTopology: samples.every((sample) => sample.signature === samples[0].signature),
    };
  });
  const representative = buildTree(r);
  return {
    residue: r,
    representative: {
      nodes: representative.nodes.length,
      edges: representative.edges.length,
      leaves: representative.leaves.length,
      maxDepth: representative.maxDepth,
      initialOddValuation: representative.initialOddValuation,
      edgesById: representative.edges,
    },
    finiteSamples,
    nineLiftDiagnostics,
  };
});

console.log(JSON.stringify({
  status: "finite exact BigInt diagnostic only; no all-index inference",
  sourceRelation: "im-results/agent10-cascade/FirstInverseComplete.lean",
  samplePeriods: SAMPLE_PERIODS,
  sampleMultipliers: SAMPLE_MULTIPLIERS,
  nineLiftPeriods: { base: NINE_LIFT_BASE_PERIOD, sample: NINE_LIFT_SAMPLE_PERIOD, offsets: NINE_LIFT_OFFSETS },
  report,
}, (_key, value) => typeof value === "bigint" ? value.toString() : value, 2));
