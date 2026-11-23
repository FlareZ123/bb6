#!/usr/bin/env node
'use strict';

/*
 * Exact dyadic inverse sieve for the interior S-parent of BB429's
 * branch-9 diagonal family. Intermediate research, not a root decision.
 *
 * The true side-parent at i=4*k+3, t=n+J-i, is
 *   X=12*2^(n+J)+6*2^t-6*2^J-8-3*k
 *   Y=24*2^(n+J)-12*2^t-12*2^J+5-6*k.
 *
 * For the depth-D certificate, J,t >= D+6 and k modulo 2^(D+6)
 * are sufficient. We use the signed 2-adic representatives
 *   (X0,Y0)=(-8-3*k,5-6*k)
 * and NEVER truncate them modulo 2^K during reverse expansion.
 *
 * Every tested residue predicate is a NECESSARY blank-root condition
 * in the specified original-source BB429 accelerated system. No
 * assertion that an allowed residue is actually root reachable.
 *
 * Source references:
 *   BB429Mod8.Allowed
 *   BB429RootEven8.rooted_positive_even_eight
 *   BB429Even16.rooted_even_sixteen
 *   BB429SevenStrong.rooted_{seven,one,five}_strong
 *   BB429ResetBoundaryRows.odd_odd_rows
 *   BB429RootMod64R{0,2}.no_*
 *
 * Exact predecessors for positive first counter >= 33:
 *   F: ((a-3)/2,a+b)                     [odd a]
 *   S: ((4a+b-26)/4,(b+4)/2)            [odd a,b=2 mod4]
 *   E: ((4a+b-14)/4,b/2)                [even a,b=2 mod4]
 *
 * The true side-parent is huge, and each <=D inverse ancestor has
 * positive first counter >=33, whenever J,t >= D+6 and J>=6.
 */

function rem(x, n) {
  const m = BigInt(n);
  return Number((x % m + m) % m);
}

function necessary(a, b) {
  const a8 = rem(a, 8), a16 = rem(a, 16), a32 = rem(a, 32);
  const a64 = rem(a, 64), b4 = rem(b, 4);
  const b8 = rem(b, 8), b16 = rem(b, 16), b32 = rem(b, 32);

  if (rem(a, 2) === 0) {
    // Positive even root: even16 strengthens even8.
    if (b16 !== (rem(a, 4) === 0 ? 2 : 10)) return false;
  } else {
    // All-time Allowed predicate from the exact source accelerator.
    const allowed =
      a8 === 1 ? b4 !== 3 :
      a8 === 3 ? b4 !== 0 :
      a8 === 5 ? true :
      a8 === 7 ? b4 === 2 || b4 === 3 : false;
    if (!allowed) return false;

    if (a8 === 7 && b8 !== 2 && b8 !== 3) return false;
    if (a16 === 1 && b8 !== 1 && b8 !== 2) return false;
    if (a32 === 5 && b8 !== 2 && b8 !== 4 && b8 !== 5) return false;

    if (rem(b, 2) === 1) {
      const required = {1:1, 3:7, 7:3, 9:1, 11:7, 15:3}[a16];
      if (required !== undefined && b8 !== required) return false;
    }
  }

  // Ten published all-time forbidden root residue cells.
  if ((a16 === 15 && b32 === 26) ||
      (a32 === 15 && b32 === 24) ||
      (a32 === 31 && b32 === 24) ||
      (a32 === 1 && b32 === 25) ||
      (a64 === 1 && b32 === 23) ||
      (a64 === 33 && b32 === 23) ||
      (a64 === 5 && b32 === 20) ||
      (a16 === 3 && b32 === 18) ||
      (a32 === 9 && b32 === 9) ||
      (a64 === 21 && b32 === 20)) return false;

  return true;
}

function parents(a, b) {
  const out = [];
  if (rem(a, 2) === 1) out.push([(a - 3n)/2n, a+b]);
  if (rem(a, 2) === 1 && rem(b, 4) === 2)
    out.push([(4n*a+b-26n)/4n, (b+4n)/2n]);
  if (rem(a, 2) === 0 && rem(b, 4) === 2)
    out.push([(4n*a+b-14n)/4n, b/2n]);
  return out;
}

function survives(k, depth) {
  let states = [[-8n-3n*k, 5n-6n*k]];
  for (let level=0; level<=depth; ++level) {
    states = states.filter(([a,b]) => necessary(a,b));
    if (states.length === 0) return false;
    if (level !== depth) states = states.flatMap(([a,b]) => parents(a,b));
  }
  return true;
}

function sieve(depth) {
  if (!Number.isInteger(depth) || depth < 0 || depth > 30)
    throw Error('Depth must be an integer from 0 to 30');
  let bits = 6;
  let surviving = Array.from({length:64},(_,i)=>BigInt(i))
    .filter(k=>survives(k,0));
  const counts = [{depth:0,bits,survivors:surviving.length}];
  for (let d=1; d<=depth; ++d) {
    const step = 1n << BigInt(bits);
    const lifts = surviving.flatMap(k=>[k,k+step]);
    bits++;
    surviving = lifts.filter(k=>survives(k,d));
    counts.push({depth:d,bits,survivors:surviving.length});
  }
  return {counts, surviving};
}

if (require.main === module) {
  const depth = process.argv[2] === undefined ? 16 : Number(process.argv[2]);
  const {counts,surviving} = sieve(depth);
  console.log('Necessary residue counts (no positive reachability asserted):');
  for (const {depth:d,bits,survivors:n} of counts)
    console.log('depth='+d+' bits='+bits+' survivors='+n+'/'+(2n**BigInt(bits)));
  if (depth >= 16 && counts[16].survivors !== 3068)
    throw Error('Regression: depth-16 count should be 3068/4194304');
  const base = [1,3,9,11,19,25,27].map(BigInt);
  const {surviving:baseCalculated} = sieve(0);
  // There are two lifts per class, 6-bit version of the 5-bit result.
  const reduced = [...new Set(baseCalculated.map(x=>Number(x%32n)))].sort((a,b)=>a-b);
  if (reduced.join(',') !== base.map(Number).join(','))
    throw Error('Regression: the mod-32 immediate sieve changed');
  console.log('k mod32 survivors at depth0:',reduced.join(','));
  console.log('Final surviving residue classes:',surviving.length);
  console.log('These classes remain OPEN; the sieve is a necessary filter only.');
}

module.exports = {necessary,parents,survives,sieve};
