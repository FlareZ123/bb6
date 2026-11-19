#!/usr/bin/env node
"use strict";

// Source-shaped #623 root replay plus the finite ternary carry-transducer check.
// This is a reproducible finite diagnostic, not an all-time nonhalting proof.

function assert(condition, message) {
  if (!condition) throw new Error(message);
}

// Exact evaluator/drain structure used by the source-shaped root replay.
function evalA(a, k, m) {
  while (true) {
    const q = k / 3n;
    const r = k % 3n;
    if (r === 2n) return [a + 1n, q, m];
    if (a === 0n) {
      if (r === 0n) return null;
      return [a, q, m];
    }
    if (r === 0n) return [a - 1n, q, m + 2n];
    a -= 1n;
    m += 2n * q + 3n;
    k = q;
  }
}

function drainB(a, b, m) {
  while (b > 0n) {
    const next = evalA(a, b - 1n, m + 2n * b + 3n);
    if (next === null) return null;
    [a, b, m] = next;
  }
  return [a, m];
}

function nextState(a, d) {
  if (a === 0n) {
    if (d % 2n === 1n) {
      const result = drainB(d + 1n, 2n, 2n);
      return result === null ? null : [result[0], result[1]];
    }
    return [d, 7n];
  }

  if (d % 2n === 1n && a >= d + 5n) {
    const result = drainB(a - d - 5n, d + 3n, 5n);
    return result === null ? null : [result[0], result[1]];
  }

  if (d % 2n === 0n && a >= d + 3n) {
    const result = drainB(a - d - 2n, d + 2n, 2n);
    return result === null ? null : [result[0], result[1]];
  }

  if (a % 2n === 1n) return null;

  if (a === d + 2n) {
    const result = drainB(0n, a, 2n);
    return result === null ? null : [result[0], result[1]];
  }

  if (d % 2n === 1n) {
    const result = drainB(d + 4n - a, a - 1n, 3n);
    return result === null ? null : [result[0], result[1]];
  }

  const evaluated = evalA(d + 1n - a, a, 2n * a + 5n);
  if (evaluated === null) return null;
  const result = drainB(evaluated[0], evaluated[1], evaluated[2]);
  return result === null ? null : [result[0], result[1]];
}

function pow3(n) {
  let value = 1n;
  for (let i = 0; i < n; i++) value *= 3n;
  return value;
}

function blockParameters(q) {
  let ell = 0n;
  let tau = 0n;
  let power = 1n;
  while (tau < q + 3n) {
    ell += 1n;
    power *= 3n;
    tau = (power - 1n) / 2n;
  }

  const correctionBound = 34n * ell + 140n;
  const terminalBound = 36n * ell + 88n;
  const B = correctionBound > terminalBound ? correctionBound : terminalBound;

  let k = 0;
  while (pow3(k) <= B) k += 1;
  let j = 0;
  while (pow3(j) <= B ** 3n) j += 1;

  assert(pow3(k) > B, "lower buffer does not dominate B");
  assert(pow3(j) > B ** 3n, "upper modulus does not dominate B^3");
  assert(j >= 3 * k - 2, "unexpected k,j relation");

  return { ell, B, k, j, blockLength: j - k - 4 };
}

function ternaryDigits(value, length) {
  const modulus = pow3(length);
  let residue = value % modulus;
  if (residue < 0n) residue += modulus;

  const digits = new Array(length);
  for (let i = 0; i < length; i++) {
    digits[i] = Number(residue % 3n);
    residue /= 3n;
  }
  return digits;
}

function digitAndCarry(raw) {
  let digit = raw % 3n;
  if (digit < 0n) digit += 3n;
  return [Number(digit), Number((raw - digit) / 3n)];
}

function euclideanMod(value, modulus) {
  let residue = value % modulus;
  if (residue < 0n) residue += modulus;
  return residue;
}

function floorDiv(value, modulus) {
  return (value - euclideanMod(value, modulus)) / modulus;
}

function coordinates(a, d) {
  const left = a >= d;
  const q = left ? d : a;
  const p = left ? a - d : d - a;
  const g = p - 3n * q;
  const oddD = d % 2n === 1n;
  const gamma = left ? (oddD ? 18n : 10n) : (oddD ? 2n : 4n);
  return { x: 2n * g - gamma, y: 6n * q, q, left };
}

function nonmonochromaticExtremeBlock(digits) {
  // Excludes both the all-zero and all-two words; an all-one word is allowed.
  return digits.some((digit) => digit !== 0) &&
    digits.some((digit) => digit !== 2);
}

function outputMiddleDigits(xDigits, yDigits, k, j, branch, initialXCarry, initialYCarry) {
  let xCarry = initialXCarry;
  let yCarry = initialYCarry;
  const output = [];

  for (let i = k; i < j - 2; i++) {
    let rawX;
    let rawY;

    if (branch === "L") {
      rawX = BigInt(xDigits[i] - yDigits[i - 1] + xCarry);
      rawY = BigInt(yDigits[i - 1] + yCarry);
    } else {
      rawX = BigInt(-xDigits[i] - xDigits[i - 1] - yDigits[i - 1] + xCarry);
      rawY = BigInt(xDigits[i - 1] + yDigits[i - 1] + yCarry);
    }

    const [outputX, nextXCarry] = digitAndCarry(rawX);
    const [outputY, nextYCarry] = digitAndCarry(rawY);

    if (i >= k + 2) output.push([outputX, outputY]);
    xCarry = nextXCarry;
    yCarry = nextYCarry;
  }

  return output;
}

function outputXMiddleBlock(xDigits, yDigits, k, j, branch, initialXCarry, initialYCarry) {
  return outputMiddleDigits(
    xDigits, yDigits, k, j, branch, initialXCarry, initialYCarry
  ).map(([outputX]) => outputX);
}

function universallySafe(x, y, q, parameters) {
  const { k, j } = parameters;
  const xDigits = ternaryDigits(x, j);
  const yDigits = ternaryDigits(y, j);
  let cases = 0;

  for (const branch of ["L", "R"]) {
    const minXCarry = branch === "L" ? -2 : -4;
    const maxXCarry = branch === "L" ? 2 : 1;

    for (let initialXCarry = minXCarry; initialXCarry <= maxXCarry; initialXCarry++) {
      for (let initialYCarry = -2; initialYCarry <= 2; initialYCarry++) {
        const block = outputXMiddleBlock(
          xDigits, yDigits, k, j, branch, initialXCarry, initialYCarry
        );
        cases += 1;
        if (!nonmonochromaticExtremeBlock(block)) {
          return { safe: false, cases };
        }
      }
    }
  }

  return { safe: true, cases };
}

// Anchor the copied root map against its first source-shaped transitions.
let anchorA = 0n;
let anchorD = 7n;
const expectedPrefix = [
  [6n, 14n],
  [6n, 31n],
  [26n, 26n],
  [2n, 83n]
];
for (let i = 0; i < expectedPrefix.length; i++) {
  const next = nextState(anchorA, anchorD);
  assert(next !== null, "root map unexpectedly halted in anchor prefix");
  [anchorA, anchorD] = next;
  assert(
    anchorA === expectedPrefix[i][0] && anchorD === expectedPrefix[i][1],
    "source-shaped root prefix mismatch at transition " + (i + 1)
  );
}

const transitions = Number(process.argv[2] || 10000);
assert(Number.isSafeInteger(transitions) && transitions >= 33, "steps must be an integer >= 33");

let a = 0n;
let d = 7n;
let checkedStates = 0;
let carryCases = 0;
let minBlockLength = Infinity;
let maxBlockLength = 0;
let firstFailure = null;
let sourceCrosscheckStates = 0;
let sourceCrosscheckDigitMismatches = 0;
let sourceCarryBoundViolations = 0;
let firstSourceMismatch = null;

for (let index = 1; index <= transitions; index++) {
  const next = nextState(a, d);
  if (next === null) {
    firstFailure = index;
    break;
  }

  // Cross-check the exact source transition against the digit transducer.
  // This covers 1,968 transitions: source indices 32 through 1,999.
  if (index >= 33 && index <= 2000) {
    const current = coordinates(a, d);
    const future = coordinates(next[0], next[1]);
    const parameters = blockParameters(current.q);
    const { k, j } = parameters;
    const branch = future.left ? "L" : "R";
    const modulus = pow3(k);
    const lowerModulus = pow3(k - 1);
    const x0 = euclideanMod(current.x, modulus);
    const x1 = euclideanMod(current.x, lowerModulus);
    const y1 = euclideanMod(current.y, lowerModulus);

    const linearX = branch === "L"
      ? current.x - 3n * current.y
      : -4n * current.x - 3n * current.y;
    const linearY = branch === "L"
      ? 3n * current.y
      : 3n * current.x + 3n * current.y;
    const correctionX = future.x - linearX;
    const correctionY = future.y - linearY;

    const lowX = branch === "L"
      ? x0 - 3n * y1
      : -x0 - 3n * x1 - 3n * y1;
    const lowY = branch === "L"
      ? 3n * y1
      : 3n * x1 + 3n * y1;
    const initialXCarry = Number(floorDiv(lowX + correctionX, modulus));
    const initialYCarry = Number(floorDiv(lowY + correctionY, modulus));

    const xDigits = ternaryDigits(current.x, j);
    const yDigits = ternaryDigits(current.y, j);
    const actualXDigits = ternaryDigits(future.x, j);
    const actualYDigits = ternaryDigits(future.y, j);
    const predicted = outputMiddleDigits(
      xDigits, yDigits, k, j, branch, initialXCarry, initialYCarry
    );

    const xCarryInBounds = branch === "L"
      ? initialXCarry >= -2 && initialXCarry <= 2
      : initialXCarry >= -4 && initialXCarry <= 1;
    if (!xCarryInBounds || initialYCarry < -2 || initialYCarry > 2) {
      sourceCarryBoundViolations += 1;
    }

    for (let offset = 0; offset < predicted.length; offset++) {
      const position = k + 2 + offset;
      if (predicted[offset][0] !== actualXDigits[position] ||
          predicted[offset][1] !== actualYDigits[position]) {
        sourceCrosscheckDigitMismatches += 1;
        if (firstSourceMismatch === null) {
          firstSourceMismatch = {
            transition: index,
            position,
            branch,
            initialXCarry,
            initialYCarry
          };
        }
      }
    }
    sourceCrosscheckStates += 1;
  }

  [a, d] = next;

  if (index < 33) continue;

  const left = a >= d;
  const q = left ? d : a;
  const p = left ? a - d : d - a;
  const g = p - 3n * q;
  const oddD = d % 2n === 1n;
  const gamma = left
    ? (oddD ? 18n : 10n)
    : (oddD ? 2n : 4n);

  const x = 2n * g - gamma;
  const y = 6n * q;
  const parameters = blockParameters(q);

  minBlockLength = Math.min(minBlockLength, parameters.blockLength);
  maxBlockLength = Math.max(maxBlockLength, parameters.blockLength);

  const result = universallySafe(x, y, q, parameters);
  carryCases += result.cases;

  if (!result.safe) {
    firstFailure = {
      index,
      a: String(a),
      d: String(d),
      q: String(q),
      x: String(x),
      ell: String(parameters.ell),
      k: parameters.k,
      j: parameters.j,
      B: String(parameters.B),
      blockLength: parameters.blockLength
    };
    break;
  }

  checkedStates += 1;
}

console.log(JSON.stringify({
  rootStart: "D(0,7)",
  transitionsRequested: transitions,
  checkedStates,
  carryCases,
  carryCasesPerState: 55,
  blockLength: { min: minBlockLength, max: maxBlockLength },
  sourceCrosscheck: {
    states: sourceCrosscheckStates,
    digitMismatches: sourceCrosscheckDigitMismatches,
    carryBoundViolations: sourceCarryBoundViolations,
    firstMismatch: firstSourceMismatch
  },
  firstFailure
}, null, 2));
