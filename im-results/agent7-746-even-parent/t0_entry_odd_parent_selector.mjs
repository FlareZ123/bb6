#!/usr/bin/env node
// O(log K) exact search for incoming odd parents of a t=0 fatal entry.
// Computes the unique possible fatal-tail depth r from K.
// See T0-FATAL-DEPTH-EXPLICIT-R.md,
// T0-ENTRY-ODD-PARENT-SELECTOR.md, and
// T0-SAME-LEVEL-DEPTH-LOG-BOUND.md.

function mod(x, m) {
  return ((x % m) + m) % m;
}

function pow2(n) {
  return 1n << BigInt(n);
}

function v3(n) {
  let v = 0;
  while (n % 3n === 0n) {
    n /= 3n;
    v++;
  }
  return v;
}

function findSourceLevel(P) {
  for (let L = 0; L <= P.toString(2).length; L++) {
    const p = pow2(L);
    if (6n * p + 1n <= P && P <= 8n * p - 1n) return L;
  }
  return null;
}

function analyze(K) {
  if (!Number.isSafeInteger(K) || K < 266) {
    throw new Error("Require integer K>=266.");
  }
  if (K % 6 !== 2 && K % 6 !== 3) {
    return { status: "outside-adjacent-fatal-K-sector" };
  }

  const k = BigInt(K);
  const p = pow2(K);
  const c = 2n * k + 7n;

  // a=floor(log2(c)); r=K+1-a is the only possible fatal-tail depth.
  let a = 0n;
  while (pow2(a + 1n) <= c) a++;
  const r = k + 1n - a;

  if (r % 2n !== 1n) {
    return { status: "no-odd-r", a: String(a), r: String(r) };
  }
  if (4n * c > 7n * pow2(a)) {
    return {
      status: "fails-t0-source-band",
      a: String(a),
      r: String(r)
    };
  }

  const B0 = c * pow2(r + 3n);
  const Dnumerator = B0 - 16n * p + 2n * k + 1n;
  if (Dnumerator % 3n !== 0n) {
    throw new Error("The K-sector and odd-r conditions should make D0 integral.");
  }

  const D0 = Dnumerator / 3n;
  const h = 8n * p + k - D0;
  if (D0 <= 0n || D0 % 2n !== 1n ||
      4n * p > h + k + 4n || h + k + 5n >= 8n * p ||
      (h + k) % 2n !== 1n) {
    throw new Error("Explicit-r candidate failed its level-K source certificate.");
  }

  const raw = 4n * p + (h + k - 1n) / 2n + 3n;
  if (raw % 2n !== 1n || raw < 6n * p + 1n || raw > 8n * p - 1n) {
    throw new Error("Explicit-r candidate failed the t=0 odd-reset band.");
  }

  const D0mod3 = mod(D0, 3n);
  if (D0mod3 === 0n) {
    return {
      status: "no-incoming-odd-parent",
      a: String(a),
      r: String(r),
      D0: String(D0),
      D0mod3: "0",
      t0SourceHeight: String(h),
      t0Raw: String(raw),
      localIncomingParents: []
    };
  }

  // A_K = 1 (mod 3). The incoming odd-parent condition fixes q parity.
  const epsilon = D0mod3 === 1n ? 1n : 0n;
  const A = 16n * p + 2n * k + 5n;
  const C = pow2(epsilon + 1n) * D0;
  if (mod(A, 3n) !== 1n || mod(C, 3n) !== 1n) {
    throw new Error("Base mod-3 selector failed.");
  }

  // The explicit D0 formula gives the stronger bound q <= a-1.
  // Enumerate only q of the forced parity.
  const qMax = K % 6 === 2 ? a - 4n : a - 3n;

  const localIncomingParents = [];
  for (let q = epsilon; q <= qMax; q += 2n) {
    const E = 8n * p + k - pow2(q) * D0;

    // E must be the first entry at level K.
    if (4n * p > E + k + 4n || E + k + 5n >= 8n * p) continue;

    const X = 2n * E + 5n;
    if (X % 3n !== 0n) continue;

    const v = v3(X);
    const t = v - 1;
    const d = X / (3n ** BigInt(v));
    const P = pow2(t) * d;
    const L = findSourceLevel(P);

    // q=2m+epsilon, so X=A-C*4^m. This checks the exact 3-adic selector.
    const m = (q - epsilon) / 2n;
    if (v3(A - C * (4n ** m)) !== v) {
      throw new Error("3-adic selector/valuation mismatch.");
    }

    if (L === null || L >= K || t > L) continue;
    const l = BigInt(L);
    const pL = pow2(L);
    const parentHeight = 2n * P - 8n * pL - l - 5n;
    const parentLevelOK =
      4n * pL <= parentHeight + l + 4n &&
      parentHeight + l + 5n < 8n * pL;
    const scaleOK = pow2(K - 2) < 3n ** BigInt(L);

    if (parentLevelOK && scaleOK) {
      localIncomingParents.push({
        q: String(q),
        incomingValuation: t,
        sourceLevel: L,
        sourceHeight: String(parentHeight),
        entryHeight: String(E),
        oddQuotient: String(d),
        sourceParameter: String(P)
      });
    }
  }

  return {
    status: "selector",
    a: String(a),
    r: String(r),
    D0: String(D0),
    D0mod3: String(D0mod3),
    forcedQParity: String(epsilon),
    qMax: String(qMax),
    localIncomingParents,
    t0SourceHeight: String(h),
    t0Raw: String(raw)
  };
}

for (const K of [266, 267, 273, 279, 309, 333, 542, 704, 1000]) {
  console.log(JSON.stringify({ K, ...analyze(K) }));
}
