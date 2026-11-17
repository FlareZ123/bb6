#!/usr/bin/env node
// Incremental all-t 3-adic selector and local source-band search for the
// incoming odd parent of a t=0 fatal entry.
// See T0-ENTRY-ODD-PARENT-SELECTOR.md.

function mod(x, m) {
  return ((x % m) + m) % m;
}

function pow2(n) {
  return 1n << BigInt(n);
}

function powMod(a, e, m) {
  let x = 1n;
  a %= m;
  while (e > 0n) {
    if (e & 1n) x = (x * a) % m;
    a = (a * a) % m;
    e >>= 1n;
  }
  return x;
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

function analyzeAll(K, r) {
  if (!Number.isSafeInteger(K) || !Number.isSafeInteger(r) ||
      K < 266 || (K % 6 !== 2 && K % 6 !== 3) ||
      r < 0 || r % 2 !== 1) {
    throw new Error("Require K>=266, K mod 6 in {2,3}, and odd r.");
  }

  const k = BigInt(K);
  const p = pow2(K);
  const Dnumerator =
    (2n * k + 7n) * pow2(r + 3) -
    16n * p + 2n * k + 1n;
  if (Dnumerator % 3n !== 0n) {
    throw new Error("The proposed (K,r) does not give integral D0.");
  }
  const D0 = Dnumerator / 3n;
  const h = 8n * p + k - D0;

  if (D0 <= 0n || D0 % 2n !== 1n ||
      4n * p > h + k + 4n || h + k + 5n >= 8n * p ||
      (h + k) % 2n !== 1n) {
    throw new Error("The proposed (K,r) is not a valid level-K t=0 source.");
  }

  const raw = 4n * p + (h + k - 1n) / 2n + 3n;
  if (raw % 2n !== 1n || raw < 6n * p + 1n || raw > 8n * p - 1n) {
    throw new Error("The proposed source fails the t=0 odd-reset band.");
  }

  const D0mod3 = mod(D0, 3n);
  if (D0mod3 === 0n) {
    return {
      status: "no-incoming-odd-parent",
      D0: String(D0),
      D0mod3: "0",
      t0SourceHeight: String(h),
      t0Raw: String(raw),
      localIncomingParents: []
    };
  }

  const epsilon = D0mod3 === 1n ? 1n : 0n;
  const A = 16n * p + 2n * k + 5n;
  const C = pow2(Number(epsilon + 1n)) * D0;
  if (mod(A, 3n) !== 1n || mod(C, 3n) !== 1n) {
    throw new Error("Base Hensel congruence failed.");
  }

  const invC = mod(C, 3n) === 1n ? 1n : 2n;
  let m = 0n;
  const localIncomingParents = [];

  // At stage t, m is the unique residue mod 3^t satisfying
  // A = C*4^m (mod 3^(t+1)); q = 2*m+epsilon mod 2*3^t.
  // Each stage adds one Hensel digit. The q representatives across all
  // stages total O(K), since their moduli grow geometrically.
  for (let t = 0; t < K; t++) {
    const qResidue = 2n * m + epsilon;
    const qModulus = 2n * (3n ** BigInt(t));
    if (qResidue > k - 1n) break;

    for (let q = qResidue; q <= k - 1n; q += qModulus) {
      const entryDeficit = pow2(Number(q)) * D0;
      const E = 8n * p + k - entryDeficit;

      // E must itself be the first entry at level K.
      if (4n * p > E + k + 4n || E + k + 5n >= 8n * p) continue;

      const X = 2n * E + 5n;
      if (v3(X) !== t + 1) continue; // exact incoming valuation

      const d = X / (3n ** BigInt(t + 1));
      const P = pow2(t) * d;
      const L = findSourceLevel(P);
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
          t,
          sourceLevel: L,
          sourceHeight: String(parentHeight),
          entryHeight: String(E),
          oddQuotient: String(d)
        });
      }
    }

    // Lift m_t mod 3^t to m_(t+1) mod 3^(t+1).
    const modulus3 = 3n ** BigInt(t + 2);
    const scale = 3n ** BigInt(t + 1);
    const residual = mod(A - C * powMod(4n, m, modulus3), modulus3);
    if (residual % scale !== 0n) {
      throw new Error("Hensel divisibility invariant failed.");
    }
    const digit = mod((residual / scale) * invC, 3n);
    m += digit * (3n ** BigInt(t));
  }

  return {
    status: "selector",
    D0: String(D0),
    D0mod3: String(D0mod3),
    forcedQParity: String(epsilon),
    localIncomingParents,
    t0SourceHeight: String(h),
    t0Raw: String(raw)
  };
}

for (const [K, r] of [
  [267, 259],
  [273, 265],
  [279, 271],
  [309, 301],
  [333, 325]
]) {
  console.log(JSON.stringify({ K, r, ...analyzeAll(K, r) }));
}
