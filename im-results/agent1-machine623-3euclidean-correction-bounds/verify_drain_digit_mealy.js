#!/usr/bin/env node
"use strict";

// Exact finite-state digit transducer for N=(2b-1+3^L)/4.
// This checks the transducer against both the closed form and the
// recursive 3-adic valuation descent. It is a diagnostic, not the proof.

const limit = Number(process.argv[2] || 100000);
if (!Number.isSafeInteger(limit) || limit < 1) {
  throw new Error("limit must be a positive safe integer");
}

function pow3(n) {
  return 3n ** BigInt(n);
}

function chooseLength(b) {
  const x = 2n * b - 1n;
  let j = 0;
  let p = 1n;
  while (p * 3n <= x) {
    p *= 3n;
    j += 1;
  }
  return (j % 2 === Number(b % 2n)) ? j : j + 1;
}

const first = [
  [2, 3],
  [1, 1],
  [0, -1]
];

const transitions = {
  "-1": [
    [1, 1],
    [0, -1],
    [2, 1]
  ],
  "1": [
    [2, 3],
    [1, 1],
    [0, -1]
  ],
  "3": [
    [0, 1],
    [2, 3],
    [1, 1]
  ]
};

function transduce(b, length) {
  let [digit, carry] = first[Number(b % 3n)];
  const digits = [digit];
  let value = BigInt(digit);
  let place = 3n;

  for (let i = 1; i < length; i += 1) {
    const inputDigit = Number((b / pow3(i)) % 3n);
    const transition = transitions[String(carry)][inputDigit];
    digit = transition[0];
    carry = transition[1];
    digits.push(digit);
    value += BigInt(digit) * place;
    place *= 3n;
  }

  return { digits, value, finalCarry: carry };
}

function valuationSignature(b) {
  let current = b;
  let signedDrop = 0n;
  let iterations = 0;

  while (current > 0n) {
    let oddPart = 2n * current - 1n;
    let valuation = 0n;

    while (oddPart % 3n === 0n) {
      oddPart /= 3n;
      valuation += 1n;
    }

    const epsilon = oddPart % 6n === 5n ? 1n : 0n;
    const next = (oddPart - 1n - 4n * epsilon) / 6n;

    if (next >= current) {
      throw new Error("valuation descent did not strictly decrease");
    }

    signedDrop += valuation + 1n - 2n * epsilon;
    iterations += 1;
    current = next;
  }

  return { signedDrop, iterations };
}

let checked = 0;
let maxLength = 0;
let maxIterations = 0;
const finalCarryCounts = { "1": 0, "3": 0 };
const outputDigitCounts = [0, 0, 0];

for (let bi = 1n; bi <= BigInt(limit); bi += 1n) {
  const length = chooseLength(bi);
  const modulus = pow3(length);
  const numerator = 2n * bi - 1n + modulus;

  if (numerator % 4n !== 0n) {
    throw new Error("normal-form numerator is not divisible by 4 at b=" + bi);
  }

  const normalFormN = numerator / 4n;
  const result = transduce(bi, length);
  const highDigit = bi / modulus;
  const expectedCarry = 1n + 2n * highDigit;

  if (result.value !== normalFormN) {
    throw new Error("transducer integer mismatch at b=" + bi);
  }
  if (BigInt(result.finalCarry) !== expectedCarry) {
    throw new Error("terminal carry mismatch at b=" + bi);
  }
  if (!(pow3(length - 1) <= normalFormN && normalFormN < modulus)) {
    throw new Error("normal-form length mismatch at b=" + bi);
  }

  const countTwo = result.digits.filter((digit) => digit === 2).length;
  const countOne = result.digits.filter((digit) => digit === 1).length;
  const transducerDrop = BigInt(length - 2 * countTwo);
  const transducerIterations = countOne + countTwo;

  const recursive = valuationSignature(bi);
  if (transducerDrop !== recursive.signedDrop ||
      BigInt(transducerIterations) !== BigInt(recursive.iterations)) {
    throw new Error("valuation signature mismatch at b=" + bi);
  }

  checked += 1;
  maxLength = Math.max(maxLength, length);
  maxIterations = Math.max(maxIterations, recursive.iterations);
  finalCarryCounts[String(result.finalCarry)] += 1;
  for (const digit of result.digits) {
    outputDigitCounts[digit] += 1;
  }
}

console.log(JSON.stringify({
  checked,
  maxLength,
  maxIterations,
  finalCarryCounts,
  outputDigitCounts
}, null, 2));
