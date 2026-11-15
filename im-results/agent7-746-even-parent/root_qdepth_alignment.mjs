#!/usr/bin/env node
/**
 * Exact BigInt scan for root/Q-depth t=1 parent alignment.
 * Mirrors im-results/agent10-cascade/root_forward_3adic.py.
 * Finite computational evidence only; not an all-time theorem.
 *
 * For a t=1 odd reset at source level K, alignment at even depth j requires
 *   9a + 2K + 7 - 2^(K+2) = (2K+7) * 2^(j+1),
 * equivalently B/8/(2K+7) = 2^(j+1), where
 *   B = 112*2^K - 2K - 34 - 18*h.
 */
const steps = Number(process.argv[2] ?? 100000);
if (!Number.isSafeInteger(steps) || steps < 0) throw new Error("steps must be nonnegative");

function firstFailedLevel(h) {
  const m = h.toString(2).length - 1;
  let k = Math.max(0, m - 2), p = 1n << BigInt(k);
  while (h + BigInt(k) + 5n >= 8n * p) { k++; p <<= 1n; }
  return k;
}
const powerOfTwo = x => x > 0n && (x & (x - 1n)) === 0n;
function v2(x) {
  let e = 0;
  while ((x & 1n) === 0n) { x >>= 1n; e++; }
  return { e, odd: x };
}

let h = 2n, k = 0, p = 1n, transitions = 0, entries = 1, maxT = 0;
let haltAfter = null, firstDivisible = null, firstMatch = null;
const c = { t1: 0, sector: 0, positive: 0, divisibleByOddFactor: 0, powerOfTwo: 0, evenDepth: 0 };

for (let step = 0; step < steps; step++) {
  if (step < 1000 && firstFailedLevel(h) !== k) throw new Error("source level mismatch");
  if (h + BigInt(k) + 4n === 4n * p) { haltAfter = transitions; break; }
  const s = h + BigInt(k);
  let child, t = 0;
  if ((s & 1n) === 0n) child = 4n * p + s / 2n;
  else {
    let d = 4n * p + s / 2n + 3n;
    while ((d & 1n) === 0n) { d >>= 1n; t++; }
    maxT = Math.max(maxT, t);
    child = (3n ** BigInt(t + 1) * d - 5n) / 2n;
    if (t === 1) {
      c.t1++;
      const n = k + 2;
      if (n % 6 === 4 || n % 6 === 5) {
        c.sector++;
        const odd = 2n * BigInt(k) + 7n;
        const B = 112n * p - 2n * BigInt(k) - 34n - 18n * h;
        if (B > 0n) {
          c.positive++;
          if (B % 8n !== 0n) throw new Error("t=1 B not divisible by 8");
          const M = B / 8n;
          if (M % odd === 0n) {
            c.divisibleByOddFactor++;
            const ratio = M / odd;
            if (firstDivisible === null) {
              const v = v2(ratio);
              firstDivisible = { step, K: k, n, q: h.toString(),
                D: (8n * p + BigInt(k) - h).toString(),
                B: B.toString(), M: M.toString(), oddFactor: odd.toString(),
                ratio: ratio.toString(), v2: v.e, oddPart: v.odd.toString(),
                powerOfTwo: powerOfTwo(ratio) };
            }
            if (powerOfTwo(ratio)) {
              c.powerOfTwo++;
              const j = ratio.toString(2).length - 2;
              if (j >= 0 && j % 2 === 0) {
                c.evenDepth++;
                if (firstMatch === null) firstMatch = { step, K: k, n, j };
              }
            }
          }
        }
      }
    }
  }
  const oldK = k;
  h = child;
  while (h + BigInt(k) + 5n >= 8n * p) { k++; p <<= 1n; }
  if (k > oldK) entries++;
  transitions++;
  if (step < 1000 && firstFailedLevel(h) !== k) throw new Error("target level mismatch");
}
console.log(JSON.stringify({
  requested: steps, transitions, haltAfter, entries, finalLevel: k,
  finalHeightBits: h.toString(2).length, maxOddExponent: maxT,
  counts: c, firstDivisible, firstMatch
}, null, 2));
