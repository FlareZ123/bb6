#!/usr/bin/env node
// Exact 3-adic selector and local source-band test for the incoming odd
// parent of a t=0 fatal entry. See T0-ENTRY-ODD-PARENT-SELECTOR.md.

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

function analyze(K, r, t) {
  if (![K, r, t].every(Number.isSafeInteger) ||
      K < 266 || (K % 6 !== 2 && K % 6 !== 3) ||
      r < 0 || r % 2 !== 1 || t < 0) {
    throw new Error("Require K>=266, K mod 6 in {2,3}, odd r, and t>=0.");
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
      h: String(h),
      raw: String(raw)
    };
  }

  const epsilon = D0mod3 === 1n ? 1n : 0n;
  const A = 16n * p + 2n * k + 5n;
  const C = pow2(Number(epsilon + 1n)) * D0;
  if (mod(A, 3n) !== 1n || mod(C, 3n) !== 1n) {
    throw new Error("Base Hensel congruence failed.");
  }

  // Lift m_t modulo 3^t from A = C*4^m (mod 3^(t+1)).
  let m = 0n;
  const invC = mod(C, 3n) === 1n ? 1n : 2n;
  for (let n = 0; n < t; n++) {
    const modulus = 3n ** BigInt(n + 2);
    const scale = 3n ** BigInt(n + 1);
    const residual = mod(A - C * powMod(4n, m, modulus), modulus);
    if (residual % scale !== 0n) {
      throw new Error("Hensel divisibility invariant failed.");
    }
    const digit = mod((residual / scale) * invC, 3n);
    m += digit * (3n ** BigInt(n));
    if (mod(A - C * powMod(4n, m, modulus), modulus) !== 0n) {
      throw new Error("Hensel lift failed.");
    }
  }

  const qResidue = 2n * m + epsilon;
  const modulus = 2n * (3n ** BigInt(t));
  const maxQ = k - 1n;
  const localParents = [];

  for (let q = qResidue; q <= maxQ; q += modulus) {
    const entryDeficit = pow2(Number(q)) * D0;
    const E = 8n * p + k - entryDeficit;
    if (4n * p > E + k + 4n || E + k + 5n >= 8n * p) continue;

    const X = 2n * E + 5n;
    if (v3(X) !== t + 1) continue;
    const d = X / (3n ** BigInt(t + 1));
    const P = pow2(t) * d;
    const L = findSourceLevel(P);
    if (L === null || L >= K) continue;

    const l = BigInt(L);
    const pL = pow2(L);
    const parentHeight = 2n * P - 8n * pL - l - 5n;
    const parentLevelOK =
      4n * pL <= parentHeight + l + 4n &&
      parentHeight + l + 5n < 8n * pL;

    if (parentLevelOK) {
      localParents.push({
        q: String(q),
        entry: String(E),
        incomingValuation: t,
        quotient: String(d),
        sourceParameter: String(P),
        sourceLevel: L,
        sourceHeight: String(parentHeight)
      });
    }
  }

  return {
    status: "selector",
    D0: String(D0),
    D0mod3: String(D0mod3),
    forcedQParity: String(epsilon),
    mResidue: String(m),
    qResidue: String(qResidue),
    modulus: String(modulus),
    localIncomingParents: localParents,
    h: String(h),
    raw: String(raw)
  };
}

for (const [K, r, t] of [
  [267, 259, 0],
  [309, 301, 1],
  [333, 325, 0]
]) {
  console.log(JSON.stringify({ K, r, t, ...analyze(K, r, t) }));
}
