'use strict';

// Deterministic single-file test for the coprime-to-3 modular lifting theorem.
// Exact BigInt independent transcription of Agent5 BB429Rank.next.
// No third-party dependencies. Run under Node.js with this file as entry point.

/** @param {bigint} x @param {bigint} m @returns {bigint} */
const mod = (x, m) => (x % m + m) % m;
/** @param {bigint} a @param {bigint} b @returns {bigint} */
function gcd(a, b) {
  while (b !== 0n) { const r = a % b; a = b; b = r; }
  return a;
}
/** @param {bigint} a @param {bigint} n @param {bigint} m @returns {bigint} */
function powerMod(a, n, m) {
  let value = 1n;
  a = mod(a, m);
  while (n !== 0n) {
    if (n & 1n) value = mod(value * a, m);
    a = mod(a * a, m);
    n >>= 1n;
  }
  return value;
}
/** @param {bigint} a @param {bigint} m @returns {bigint} */
function inverse(a, m) {
  if (m === 1n) return 0n;
  let r = mod(a, m), s = m, x = 1n, y = 0n;
  while (s !== 0n) {
    const q = r / s;
    [r, s] = [s, r - q * s];
    [x, y] = [y, x - q * y];
  }
  if (r !== 1n) throw new Error('Noninvertible lift coefficient');
  return mod(x, m);
}
/** @param {bigint} q @returns {bigint} */
function orderTwo(q) {
  if (q === 1n) return 1n;
  let p = 1n, x = 2n % q;
  while (x !== 1n) {
    x = x * 2n % q;
    p++;
    if (p >= q) throw new Error('Order bound failed');
  }
  return p;
}
/**
 * Construct n >= lower with A*2^n - 3n = target (mod m).
 * The recursive modulus is gcd(m, ord_oddPart(2)) < m.
 * @param {bigint} m @param {bigint} target @param {bigint} A
 * @param {bigint} lower @returns {bigint}
 */
function solveExponent(m, target, A, lower) {
  if (m === 1n) return lower;
  let q = m, a = 0n;
  while ((q & 1n) === 0n) { q /= 2n; a++; }
  const p = orderTwo(q), g = gcd(m, p);
  if (g >= m) throw new Error('Inductive descent failed');
  const n = solveExponent(g, target, A, lower > a ? lower : a);
  const f = mod(A * powerMod(2n, n, m) - 3n * n, m);
  const delta = mod(target - f, m);
  if (delta % g !== 0n) throw new Error('Gcd congruence failed');
  const h = m / g;
  const v = mod((delta / g) * inverse(mod(-3n * p / g, h), h), h);
  const answer = n + p * v;
  if (mod(A * powerMod(2n, answer, m) - 3n * answer - target, m) !== 0n) {
    throw new Error('Lift verification failed');
  }
  return answer;
}
/**
 * Explicit synthetic halt witness with original first-counter u.
 * @param {bigint} u @param {bigint} w @param {bigint} m
 * @returns {{n:bigint,W:bigint}}
 */
function witness(u, w, m) {
  if (m < 1n || gcd(m, 3n) !== 1n) throw new Error('Modulus must be positive and prime to 3');
  const A = 4n * (u + 3n);
  const n = solveExponent(m, 2n * u + w + 13n, A, u + w + 2n);
  const W = A * (2n ** n) - (2n * u + 3n * n + 13n);
  if (W < w || mod(W - w, m) !== 0n) throw new Error('Incorrect seed congruence');
  return { n, W };
}
/**
 * The entire twelve-branch source map, preserving order and Nat subtraction.
 * @param {bigint} u @param {bigint} w
 * @returns {[bigint,bigint] | null}
 */
function next(u, w) {
  const d = u - w / 2n;
  if (w >= 2n * u + 3n) return [2n * u + 3n, w - 2n * u - 3n];
  if (w === 2n * u + 2n) return [0n, 4n * u + 18n];
  if (w === 2n * u + 1n) return [11n, 4n * u + 2n];
  if (w === 2n * u) return [0n, 4n * u + 12n];
  if (w % 2n === 0n) {
    if (d === 1n) return [0n, 2n * w + 12n];
    if (d % 2n === 0n) return [11n, 2n * u + w - 2n];
    return [0n, 2n * u + w + 10n];
  }
  if (d === 1n) return null;
  if (d === 2n) return [0n, 2n * w + 8n];
  if (d % 2n === 0n) {
    if (w === 1n) return [11n, 2n * u + 10n];
    return [d + 7n, 2n * w - 4n];
  }
  return [d + 3n, 2n * w];
}
/** @param {bigint} m @param {bigint} u @param {bigint} w @returns {bigint} */
function check(m, u, w) {
  const { n, W } = witness(u, w, m);
  let state = [u, W];
  for (let i = 0n; i < n; ++i) {
    const nextState = next(...state);
    if (nextState === null || nextState[0] !== 2n * state[0] + 3n) {
      throw new Error('Expected exact first branch failed');
    }
    state = nextState;
  }
  if (next(...state) !== null || state[1] + 1n !== 2n * state[0]) {
    throw new Error('Halting line did not follow source run');
  }
  return n;
}
/** @param {bigint} n @returns {[bigint,bigint]} */
function blankCheckpoint(n) {
  let state = [0n, 0n];
  for (let i = 0n; i < n; ++i) {
    const later = next(...state);
    if (later === null) throw new Error('Unexpected blank-root halt');
    state = later;
  }
  return state;
}
function main() {
  const expected = [[50n, 109n, 66n], [51n, 11n, 282n],
                    [79n, 189n, 48n], [170n, 221n, 366n]];
  for (const [n, u, w] of expected) {
    const [x, y] = blankCheckpoint(n);
    if (x !== u || y !== w) throw new Error('Published blank checkpoint mismatch');
  }
  let count = 0, maximum = 0n;
  for (let m = 1n; m <= 100n; m++) {
    if (gcd(m, 3n) !== 1n) continue;
    for (let u = 0n; u <= 2n; u++) for (let w = 0n; w <= 2n; w++) {
      const n = check(m, u, w);
      if (n > maximum) maximum = n;
      count++;
    }
  }
  for (const m of [125n, 169n, 200n]) {
    const n = check(m, 0n, 0n);
    if (n > maximum) maximum = n;
    count++;
  }
  console.log(`PASS: ${count} exact source-map synthetic halts, max first-burst length ${maximum}`);
  console.log('Checked four independently published genuine blank-root checkpoints.');
  console.log('Finite checks corroborate, but do not prove, the all-natural theorem.');
}
if (require.main === module) main();
module.exports = { witness, solveExponent, next, check };
