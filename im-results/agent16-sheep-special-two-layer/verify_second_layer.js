#!/usr/bin/env node
"use strict";
/*
 * Exact arithmetic sanity check for the all-exponent proofs in README.md.
 * No floating point, no simulation of the original machine, no heuristic depth.
 * The theorems are the written modular arguments; this finite test supplements them.
 */
const assert = require("node:assert/strict");

function evenParents(y) {
  assert(y >= 6n && (y & 1n) === 0n);
  const delta = y - 1n;
  const out = [];
  let p3 = 1n;
  for (let h = 0; delta % p3 === 0n; h++, p3 *= 3n) {
    const z = 1n + (1n << BigInt(h)) * (delta / p3);
    const maxB = z.toString(2).length;
    for (let b = 1; b <= maxB; b++) {
      const B = BigInt(b);
      const pow = 1n << B;
      const den = 2n * pow + 1n;
      const num = 2n * z - 2n * B + 1n;
      if (num >= 5n * den && num % den === 0n) {
        const v = num / den;
        if ((v & 1n) === 1n) out.push({ h, b, x: pow * v, kind: "generic" });
      }
      if (z === 3n * pow + B + 3n) {
        out.push({ h, b, x: 3n * pow, kind: "special" });
      }
    }
  }
  return out;
}

function xTwo(a) {
  return 4n * ((1n << BigInt(a + 1)) - 1n) / 3n;
}
function isNewClass(a) {
  return (a % 6 === 5 && a % 8 !== 5 && a % 18 !== 11) ||
    (a % 6 === 3 && a % 8 !== 5 && a % 30 !== 3);
}
function expectedSecond(a) {
  const result = [];
  if (a % 18 === 11) {
    result.push({
      h: 0, b: 2,
      x: 4n * ((1n << BigInt(a + 4)) - 17n) / 27n,
      kind: "generic"
    });
  }
  if (a % 30 === 3 && a >= 33) {
    result.push({
      h: 0, b: 4,
      x: 16n * ((1n << BigInt(a + 4)) - 29n) / 99n,
      kind: "generic"
    });
  }
  return result;
}
function sameParents(a, actual, expected) {
  const encode = p => [p.h, p.b, p.x.toString(), p.kind].join("/");
  assert.deepEqual(
    actual.map(encode).sort(), expected.map(encode).sort(), "a=" + a
  );
}

let grammarCases = 0, newBlankExclusions = 0;
for (let a = 3; a <= 950; a += 2) {
  if (a % 6 === 1) continue;
  const X = xTwo(a);
  sameParents(a, evenParents(X), expectedSecond(a));
  grammarCases++;

  if (isNewClass(a)) {
    const Y = 3n << BigInt(a);
    const top = evenParents(Y);
    assert.equal(top.length, 1, "direct parent count a=" + a);
    assert.equal(top[0].x, X, "direct parent identity a=" + a);
    assert.equal(evenParents(X).length, 0, "second parent count a=" + a);
    assert(X > 10n && Y > 10n);
    newBlankExclusions++;
  }
}
const A5 = Array.from({length: 72}, (_,a) => a).filter(a =>
  a % 6 === 5 && a % 8 !== 5 && a % 18 !== 11);
const A3 = Array.from({length: 120}, (_,a) => a).filter(a =>
  a % 6 === 3 && a % 8 !== 5 && a % 30 !== 3);
assert.deepEqual(A5, [17,23,35,41,59,71]);
assert.deepEqual(A3, [9,15,27,39,51,57,75,81,87,99,105,111]);
const new360 = Array.from({length: 360}, (_,a) => a).filter(isNewClass);
const old360 = Array.from({length: 360}, (_,a) => a).filter(a => a % 4 === 2);
assert.equal(new360.length, 66);
assert.equal(old360.length, 90);
assert(new360.every(a => a % 4 !== 2));
assert.equal(new Set([...new360,...old360]).size, 156);
console.log(JSON.stringify({
  verified_odd_a_up_to: 950,
  full_second_parent_grammar_cases: grammarCases,
  new_two_generation_exclusion_instances: newBlankExclusions,
  new_excluded_residue_classes_mod_360: new360.length,
  old_no_incoming_residue_classes_mod_360: old360.length,
  combined_residue_classes_mod_360: 156
}, null, 2));
