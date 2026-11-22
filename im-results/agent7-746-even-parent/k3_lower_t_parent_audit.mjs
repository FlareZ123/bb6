#!/usr/bin/env node
// Exact BigInt audit of the omitted lower-t ResetParent branches.
// Reproduces the four a=15, K in W, high-Y non-high third-lift examples.
// No floating-point arithmetic is used for parent existence or band tests.

const a = 15n;
const candidates = [25815n, 25977n, 26301n, 26463n];
const bitLength = (n) => n === 0n ? 0 : n.toString(2).length;

function v3(n) {
  let t = 0;
  while (n > 0n && n % 3n === 0n) {
    n /= 3n;
    t++;
  }
  return t;
}

function ratio(n, p) {
  // Ratios are only display metadata; all decisions below are exact.
  return Number((n * 1000000n) / p) / 1000000;
}

function mod(n, m) { return ((n % m) + m) % m; }
function pow2Mod(e, m) {
  let v = 1n, b = 2n % m;
  while (e > 0n) {
    if (e & 1n) v = v * b % m;
    b = b * b % m;
    e >>= 1n;
  }
  return v;
}

function parents(u) {
  const out = [];

  // The even band is unique; any member has bitLength = k + 3.
  const ke = BigInt(bitLength(u) - 3);
  if (ke >= 0n) {
    const q = 1n << ke;
    if (6n * q - 1n <= u && u <= 8n * q - 3n) {
      const h = 2n * u - 8n * q - ke;
      out.push({ type: "even", t: null, k: ke, source: null, parent: h });
    }
  }

  // Enumerate every t < v3(2u+5), not only the maximal valuation.
  const z = 2n * u + 5n;
  const v = v3(z);
  let pow3 = 3n;
  for (let t = 0; t < v; t++) {
    if (t > 0) pow3 *= 3n;
    const d = z / pow3;
    if (d % 2n !== 1n) continue;

    const source = (1n << BigInt(t)) * d;
    const k = BigInt(bitLength(source) - 3);
    if (k < 0n) continue;
    const q = 1n << k;
    if (6n * q + 1n <= source && source <= 8n * q - 1n) {
      const h = 2n * source - 8n * q - k - 5n;
      if (z !== pow3 * d || 2n * source !== 8n * q + h + k + 5n) {
        throw new Error("odd ResetParent identity failed");
      }
      out.push({ type: "odd", t, k, source, parent: h });
    }
  }
  return out;
}

function audit(K) {
  const p = 1n << K;
  const c = 2n * K + 7n;
  const twoA = 1n << a;

  // Exact W test: 803/512 <= c/2^a <= 1659/1024.
  if (803n * twoA > 512n * c || 1024n * c > 1659n * twoA) {
    throw new Error(`K=${K} is outside W`);
  }
  if (K % 6n !== 3n || K % 162n !== 57n || (K % 486n !== 57n && K % 486n !== 219n)) {
    throw new Error(`K=${K} is not one of the two non-high K1 residues`);
  }

  // Verify that this is the high X phase and a non-high Y third-lift.
  const e = K + 4n - a;
  const T243 = mod(80n * pow2Mod(K, 243n) + 2n * K + 13n
    - 2n * mod((2n * K + 7n) * pow2Mod(e, 243n), 243n), 243n);
  if (T243 % 3n !== 0n) throw new Error("T not divisible by 3");
  const X81 = T243 / 3n;
  if (X81 % 3n !== 0n) throw new Error("X not divisible by 3");
  const h27 = mod(2n * (X81 / 3n) - 4n * pow2Mod(K, 27n) - K - 4n, 27n);
  const Y27 = mod(2n * h27 + 5n, 27n);
  if (Y27 !== 9n && Y27 !== 18n) throw new Error(`unexpected Y mod 27: ${Y27}`);

  const B = c * (1n << (K + 4n - a));
  const numerator = 40n * p + K - 1n - B;
  if (numerator % 3n !== 0n) throw new Error("E numerator not divisible by 3");
  const E = numerator / 3n;

  const queue = [{ u: E, depth: 0 }];
  const seen = new Set();
  let root = false;
  let leaves = 0;
  let branch = false;
  const path = [];
  let u = E;

  // These four test cases have a unique parent at every nonterminal node.
  for (let depth = 0; depth < 20; depth++) {
    const ps = parents(u);
    path.push({
      targetRatio: ratio(u, p),
      valuation: v3(2n * u + 5n),
      parents: ps.map(q => ({
        type: q.type,
        t: q.t,
        k: q.k.toString(),
        sourceRatio: q.source === null ? null : ratio(q.source, p),
        parentRatio: ratio(q.parent, p)
      }))
    });
    if (ps.length === 0) break;
    if (ps.length !== 1) {
      branch = true;
      break;
    }
    u = ps[0].parent;
  }

  while (queue.length) {
    const cur = queue.shift();
    const key = cur.u.toString();
    if (seen.has(key)) continue;
    seen.add(key);
    if (cur.u === 2n) {
      root = true;
      break;
    }
    const ps = parents(cur.u);
    if (ps.length === 0) {
      leaves++;
      continue;
    }
    for (const q of ps) queue.push({ u: q.parent, depth: cur.depth + 1 });
  }

  return {
    K: K.toString(),
    Kmod486: (K % 486n).toString(),
    x: `${c}/${twoA}`,
    Ymod27: Y27.toString(),
    exploredNodes: seen.size,
    leaves,
    reachesRoot: root,
    singleParentChain: !branch,
    path
  };
}

for (const K of candidates) {
  console.log(JSON.stringify(audit(K), (_, v) => typeof v === "bigint" ? v.toString() : v, 2));
}
