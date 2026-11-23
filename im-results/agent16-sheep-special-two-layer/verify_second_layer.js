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
function zOne(a) {
  return 2n * (3n * (1n << BigInt(a + 1)) - 1n) / 5n;
}
function isNewClass(a) {
  return ([13,121].includes(a % 162) && a % 8 !== 5 &&
      a % 12 !== 1 && a % 486 !== 445) ||
    (a % 18 === 13 && a % 54 !== 13 && a % 8 !== 5 &&
      a % 12 !== 1 && a % 162 !== 103) ||
    (a % 6 === 1 && a % 18 !== 13 && a % 8 !== 5 &&
      a % 12 !== 1 && a % 54 !== 37) ||
    (a % 4 === 0 && [0, 12, 16].includes(a % 20)) ||
    (a % 6 === 5 && a % 8 !== 5 && a % 18 !== 11) ||
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
function expectedOneHiddenSecond(a) {
  const result = [];
  if (a % 12 === 1) {
    result.push({h: 1, b: 1,
      x: 2n * ((1n << BigInt(a + 5)) - 19n) / 45n,
      kind: "generic"});
  }
  if (a % 54 === 37) {
    result.push({h: 1, b: 2,
      x: 4n * ((1n << BigInt(a + 5)) - 37n) / 81n,
      kind: "generic"});
  }
  if (a % 24 === 13) {
    result.push({h: 1, b: 3,
      x: 8n * ((1n << BigInt(a + 5)) - 55n) / 153n,
      kind: "generic"});
  }
  return result;
}
function expectedTwoHiddenSecond(a) {
  const result = [];
  if (a % 12 === 1) {
    result.push({h: 1, b: 1,
      x: 2n * ((1n << BigInt(a + 5)) - 19n) / 45n,
      kind: "generic"});
  }
  if (a % 24 === 13) {
    result.push({h: 1, b: 3,
      x: 8n * ((1n << BigInt(a + 5)) - 55n) / 153n,
      kind: "generic"});
  }
  if (a % 162 === 103) {
    result.push({h: 2, b: 2,
      x: 4n * ((1n << BigInt(a + 6)) - 83n) / 243n,
      kind: "generic"});
  }
  return result;
}
function expectedThreeHiddenSecond(a) {
  const result = [];
  if (a % 12 === 1) {
    result.push({h: 1, b: 1,
      x: 2n * ((1n << BigInt(a + 5)) - 19n) / 45n,
      kind: "generic"});
  }
  if (a % 24 === 13) {
    result.push({h: 1, b: 3,
      x: 8n * ((1n << BigInt(a + 5)) - 55n) / 153n,
      kind: "generic"});
  }
  if (a % 108 === 13) {
    result.push({h: 3, b: 1,
      x: 2n * ((1n << BigInt(a + 7)) - 31n) / 405n,
      kind: "generic"});
  }
  if (a % 486 === 445) {
    result.push({h: 3, b: 2,
      x: 4n * ((1n << BigInt(a + 7)) - 193n) / 729n,
      kind: "generic"});
  }
  return result;
}
function expectedEvenSecond(a) {
  const result = [];
  if (a % 20 === 4) {
    result.push({ h: 0, b: 1,
      x: 2n * (3n * (1n << BigInt(a + 3)) - 9n) / 25n,
      kind: "generic" });
  }
  if (a % 20 === 8) {
    result.push({ h: 0, b: 4,
      x: 16n * (3n * (1n << BigInt(a + 3)) - 39n) / 165n,
      kind: "generic" });
  }
  return result;
}
function sameParents(a, actual, expected) {
  const encode = p => [p.h, p.b, p.x.toString(), p.kind].join("/");
  assert.deepEqual(
    actual.map(encode).sort(), expected.map(encode).sort(), "a=" + a
  );
}

let grammarCases = 0, evenGrammarCases = 0, newBlankExclusions = 0;
for (let a = 3; a <= 950; a += 2) {
  if (a % 162 === 67) continue;
  if (a < 7 && a % 6 === 1) continue;
  const X = xTwo(a);
  sameParents(a, evenParents(X),
    a % 6 !== 1 ? expectedSecond(a) :
      (a % 18 !== 13 ? expectedOneHiddenSecond(a) :
        (a % 54 !== 13 ? expectedTwoHiddenSecond(a) : expectedThreeHiddenSecond(a))));
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
for (let a = 4; a <= 950; a += 4) {
  const Z = zOne(a);
  sameParents(a, evenParents(Z), expectedEvenSecond(a));
  evenGrammarCases++;
  if (isNewClass(a)) {
    const Y = 3n << BigInt(a);
    const top = evenParents(Y);
    assert.equal(top.length, 1, "even direct parent count a=" + a);
    assert.equal(top[0].x, Z, "even direct parent identity a=" + a);
    assert.equal(evenParents(Z).length, 0, "even second parent count a=" + a);
    assert(Z > 10n && Y > 10n);
    newBlankExclusions++;
  }
}
const A5 = Array.from({length: 72}, (_,a) => a).filter(a =>
  a % 6 === 5 && a % 8 !== 5 && a % 18 !== 11);
const A3 = Array.from({length: 120}, (_,a) => a).filter(a =>
  a % 6 === 3 && a % 8 !== 5 && a % 30 !== 3);
assert.deepEqual(A5, [17,23,35,41,59,71]);
assert.deepEqual(A3, [9,15,27,39,51,57,75,81,87,99,105,111]);
const A1 = Array.from({length: 216}, (_,a) => a).filter(a =>
  a % 6 === 1 && a % 18 !== 13 && a % 8 !== 5 &&
  a % 12 !== 1 && a % 54 !== 37);
assert.deepEqual(A1, [7,19,43,55,79,115,127,151,163,187]);
const A2 = Array.from({length: 648}, (_,a) => a).filter(a =>
  a % 18 === 13 && a % 54 !== 13 && a % 8 !== 5 &&
  a % 12 !== 1 && a % 162 !== 103);
assert.deepEqual(A2, [31,139,211,247,319,355,463,535,571,643]);
const A3prime = Array.from({length: 1944}, (_,a) => a).filter(a =>
  [13,121].includes(a % 162) && a % 8 !== 5 &&
  a % 12 !== 1 && a % 486 !== 445);
assert.deepEqual(A3prime, [175,283,499,607,823,1147,1255,1471,1579,1795]);
const new9720 = Array.from({length: 9720}, (_,a) => a).filter(isNewClass);
const old9720 = Array.from({length: 9720}, (_,a) => a).filter(a => a % 4 === 2);
assert.equal(new9720.length, 3890);
assert.equal(old9720.length, 2430);
assert(new9720.every(a => a % 4 !== 2));
assert.equal(new Set([...new9720,...old9720]).size, 6320);
console.log(JSON.stringify({
  verified_odd_a_up_to: 950,
  odd_second_parent_grammar_cases: grammarCases,
  even_second_parent_grammar_cases: evenGrammarCases,
  new_two_generation_exclusion_instances: newBlankExclusions,
  new_excluded_residue_classes_mod_9720: new9720.length,
  old_no_incoming_residue_classes_mod_9720: old9720.length,
  combined_residue_classes_mod_9720: 6320
}, null, 2));
