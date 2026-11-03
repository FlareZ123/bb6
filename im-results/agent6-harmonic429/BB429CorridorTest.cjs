'use strict';

const assert = require('node:assert/strict');
const { performance } = require('node:perf_hooks');

/** @typedef {[bigint, bigint]} State */

/** Faithful transcription of pinned Cryptids highLevelNext. @param {State} s @returns {State|null} */
function next([u, w]) {
  if (w >= 2n * u + 3n) return [2n * u + 3n, w - 2n * u - 3n];
  if (w === 2n * u + 2n) return [0n, 4n * u + 18n];
  if (w === 2n * u + 1n) return [11n, 4n * u + 2n];
  if (w === 2n * u) return [0n, 4n * u + 12n];
  const d = u - w / 2n;
  if (w % 2n === 0n) {
    if (d === 1n) return [0n, 2n * w + 12n];
    if (d % 2n === 0n) return [11n, 2n * u + w - 2n];
    return [0n, 2n * u + w + 10n];
  }
  if (d === 1n) return null;
  if (d === 2n) return [0n, 2n * w + 8n];
  if (d % 2n === 0n) return w === 1n ? [11n, 2n * u + 10n] : [d + 7n, 2n * w - 4n];
  return [d + 3n, 2n * w];
}

/** @param {State} start @param {number} count @returns {State|null} */
function ordinary(start, count) {
  let s = start;
  for (let i = 0; i < count; i += 1) {
    if (s === null) return null;
    s = next(s);
  }
  return s;
}

const raysU = new Map();
const raysV = new Map();
for (let k = 0; k < 80; k += 1) {
  raysU.set(3n * ((1n << BigInt(k)) - 1n), k);
  raysV.set(14n * (1n << BigInt(k)) - 3n, k);
}

/** @typedef {{family:string,k:number,delta:bigint,span:number,loops:bigint}} Skip */
/**
 * Safe macro candidate. Preconditions match the four Lean ladder theorems.
 * The final-guard condition is conservative, allowing fewer skips than valid.
 * @param {State} s @param {number} remaining @returns {Skip|null}
 */
function skipCandidate([u,w],remaining) {
  let k = raysU.get(u);
  let family, delta, span, loops;
  if (k !== undefined && k >= 1) {
    if (k % 4 === 2 && w % 4n === 0n && w + 4n <= 2n*u) {
      family='U-even';delta=3n*BigInt(k)+10n;span=k+1;
      loops=(2n*u-w-4n)/delta;
    } else if (k % 4 === 1 && w % 4n === 1n && 3n*w <= 2n*u+1n) {
      family='U-odd';delta=3n*BigInt(k)+17n;span=k+2;
      loops=(2n*u+1n-3n*w)/(3n*delta);
    }
  }
  if (loops === undefined) {
    k = raysV.get(u);
    if (k !== undefined) {
      if (k % 4 === 0 && w % 4n === 2n && w + 4n <= 2n*u) {
        family='V-even';delta=3n*BigInt(k)+20n;span=k+1;
        loops=(2n*u-w-4n)/delta;
      } else if (k % 4 === 3 && w % 4n === 3n && 3n*w <= 2n*u+15n) {
        family='V-odd';delta=3n*BigInt(k)+31n;span=k+2;
        loops=(2n*u+15n-3n*w)/(3n*delta);
      }
    }
  }
  if (loops === undefined) return null;
  const cap = BigInt(Math.floor(remaining/span));
  if (loops > cap) loops = cap;
  if (loops === 0n) return null;
  return {family,k,delta,span,loops};
}

/** @param {number} horizon @param {boolean} verifySkipped @returns {{state:State|null,skips:Skip[],plain:number}} */
function accelerated(horizon,verifySkipped) {
  let s = /** @type {State|null} */ ([0n,0n]);
  let i = 0, plain = 0;
  /** @type {Skip[]} */ const skips=[];
  while (i < horizon && s !== null) {
    const candidate = skipCandidate(s,horizon-i);
    if (candidate) {
      const {family,k,delta,span,loops}=candidate;
      const ending = /** @type {State} */ ([s[0],s[1]+loops*delta]);
      const raw = Number(loops)*span;
      if (verifySkipped) assert.deepStrictEqual(ordinary(s,raw),ending,
        `${family} k=${k} at accelerated step ${i}`);
      skips.push(candidate);
      i += raw;
      s = ending;
    } else {
      s = next(s);
      plain += 1;
      i += 1;
    }
  }
  assert.equal(i,horizon,'unexpected early machine halt');
  return {state:s,skips,plain};
}

function main() {
  const N = 3_000_000;
  const t0 = performance.now();
  const slow = ordinary([0n,0n],N);
  const t1 = performance.now();
  const fast = accelerated(N,true);
  const t2 = performance.now();
  assert.deepStrictEqual(fast.state,slow);
  assert.deepStrictEqual(fast.state,[45n,11193578n]);
  const classes = new Map();
  for (const s of fast.skips) classes.set(s.family,(classes.get(s.family)??0n)+s.loops);
  assert.equal(classes.get('U-even'),26624n);
  assert.equal(classes.get('U-odd'),4168n);
  assert.equal(classes.get('V-even'),8337n);
  assert.equal(classes.get('V-odd'),2475n);
  assert.equal(fast.skips.length,15);
  console.log('PASS original blank seed,',N,'source-transcribed accelerated transitions');
  console.log('PASS',fast.skips.length,'independently checked multi-step corridor blocks');
  console.log('End state',fast.state.map(String),'plain step count',fast.plain);
  console.log('Ladder loops per family',Object.fromEntries([...classes].map(([name,n])=>[name,n.toString()])));
  console.log('Wall clock naive',Math.round(t1-t0),'ms, verified corridor',Math.round(t2-t1),'ms');
}
main();
