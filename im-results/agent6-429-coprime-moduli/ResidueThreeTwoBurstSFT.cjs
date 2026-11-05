'use strict';

/**
 * Exact BigInt test of two all-parameter synthetic halting families.
 * Independent transcription of the twelve branches in Agent5 BB429Rank.next.
 * No dependencies; never treats a synthetic start as a genuine blank orbit.
 *
 * @param {bigint} u
 * @param {bigint} w
 * @returns {[bigint,bigint] | null}
 */
function next(u, w) {
  const m = w / 2n;
  if (w >= 2n * u + 3n) return [2n * u + 3n, w - 2n * u - 3n];
  if (w === 2n * u + 2n) return [0n, 4n * u + 18n];
  if (w === 2n * u + 1n) return [11n, 4n * u + 2n];
  if (w === 2n * u) return [0n, 4n * u + 12n];
  const d = u - m;
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

/** @param {bigint} u @param {bigint} w @param {bigint} length
 * @returns {[bigint,bigint]} */
function firstBurst(u, w, length) {
  for (let i = 0n; i < length; i++) {
    const nextU = 2n * u + 3n;
    const nextW = w - nextU;
    const got = next(u, w);
    if (got === null || got[0] !== nextU || got[1] !== nextW) {
      throw new Error(`Invalid first burst at i=${i}, u=${u}, w=${w}`);
    }
    [u, w] = got;
  }
  return [u, w];
}

/** @param {bigint} t @returns {{start:bigint, time:bigint, terminal:[bigint,bigint]}} */
function classOne(t) {
  if (t < 5n || t % 4n !== 1n) throw new Error('Class one requires t>=5 and t%4=1');
  const W = 12n * (2n ** t) - 6n * t - 23n;
  const a = 3n * (2n ** t) - 3n;
  const b = 6n * (2n ** t) - 3n * t - 17n;
  const s = firstBurst(0n, W, t);
  if (s[0] !== a || s[1] !== b || W % 3n !== 1n) throw new Error('Class-one prefix identity');
  const reset = next(a, b);
  const X = 12n * (2n ** t) - 3n * t - 13n;
  if (reset === null || reset[0] !== 0n || reset[1] !== X) throw new Error('Class-one reset identity');
  const terminal = firstBurst(0n, X, t);
  if (terminal[0] !== a || terminal[1] !== 2n * a - 1n || next(...terminal) !== null) {
    throw new Error('Class-one terminal assertion');
  }
  return { start: W, time: 2n * t + 1n, terminal };
}

/** @param {bigint} c @returns {{start:bigint, time:bigint, terminal:[bigint,bigint]}} */
function classZero(c) {
  if (c < 2n) throw new Error('Class zero requires c>=2');
  const z = 2n ** c;
  const k = 4n * z - 11n, n = k + c + 1n;
  const W = 12n * (2n ** n) - 24n * z + 39n - 3n * c;
  const a = 3n * (2n ** n) - 3n;
  const b = 2n * a + 21n - 12n * z;
  const s = firstBurst(0n, W, n);
  if (s[0] !== a || s[1] !== b || W % 3n !== 0n) throw new Error('Class-zero prefix identity');
  const d = 6n * z - 10n;
  if (b % 2n !== 1n || d % 2n !== 0n || d < 4n) throw new Error('Class-zero branch guard');
  const reset = next(a, b);
  if (reset === null || reset[0] !== d + 7n || reset[1] !== 2n * b - 4n) {
    throw new Error('Class-zero branch identity');
  }
  const terminal = firstBurst(...reset, k);
  if (terminal[0] !== a || terminal[1] !== 2n * a - 1n || next(...terminal) !== null) {
    throw new Error('Class-zero terminal assertion');
  }
  return { start: W, time: n + 1n + k, terminal };
}

function main() {
  for (const t of [5n, 9n, 13n, 17n, 21n, 25n, 29n]) {
    const result = classOne(t);
    console.log(`CLASS 1 t=${t} time=${result.time} start=${result.start} terminal=(${result.terminal})`);
  }
  for (const c of [2n, 3n, 4n, 5n, 6n, 7n]) {
    const result = classZero(c);
    console.log(`CLASS 0 c=${c} time=${result.time} start-digits=${result.start.toString().length} terminal-u-digits=${result.terminal[0].toString().length}`);
  }
  console.log('PASS: 13 exact-map synthetic halts, all intermediate branches and final halting states verified.');
}
if (require.main === module) main();
module.exports = { next, firstBurst, classOne, classZero };
