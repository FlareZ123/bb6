#!/usr/bin/env node
// Exact 3-adic selector for the incoming odd parent of a t=0 fatal entry.
// The mathematical derivation is in T0-ENTRY-ODD-PARENT-SELECTOR.md.

function mod(x, m) {
  return ((x % m) + m) % m;
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

function qSelector(K, r, t) {
  if (![K, r, t].every(Number.isSafeInteger) ||
      K < 0 || r < 0 || t < 0) {
    throw new Error("Require nonnegative safe integers K, r, t.");
  }

  const k = BigInt(K);
  const p = 2n ** k;
  const Dnumerator =
    (2n * k + 7n) * (2n ** BigInt(r + 3)) -
    16n * p + 2n * k + 1n;

  if (Dnumerator % 3n !== 0n) {
    throw new Error("The proposed (K,r) does not give integral D0.");
  }
  const D0 = Dnumerator / 3n;
  const D0mod3 = mod(D0, 3n);

  if (D0mod3 === 0n) {
    return {
      status: "no-incoming-odd-parent",
      D0: String(D0),
      D0mod3: "0"
    };
  }

  // epsilon is the parity forced by 2^(q+1)*D0 = 1 (mod 3).
  const epsilon = D0mod3 === 1n ? 1n : 0n;
  const A = 16n * p + 2n * k + 5n;
  const C = (2n ** (epsilon + 1n)) * D0;
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
  const candidates = [];
  for (let q = qResidue; q <= maxQ; q += modulus) {
    candidates.push(String(q));
  }

  return {
    status: "selector",
    D0: String(D0),
    D0mod3: String(D0mod3),
    parity: String(epsilon),
    mResidue: String(m),
    qResidue: String(qResidue),
    modulus: String(modulus),
    candidatesUpToKMinus1: candidates
  };
}

const examples = [
  [267, 259, 0],
  [309, 301, 1],
  [333, 325, 0]
];

for (const [K, r, t] of examples) {
  console.log(JSON.stringify({ K, r, t, ...qSelector(K, r, t) }));
}
