'use strict';
const assert = require('node:assert/strict');

/** @param {bigint} u @param {bigint} w @returns {{u:bigint,w:bigint,steps:number}} */
function burst(u, w) {
  let steps = 0;
  while (w >= 2n * u + 3n) {
    const take = 2n * u + 3n;
    u = take;
    w -= take;
    steps++;
  }
  return {u, w, steps};
}

/** @param {bigint} u @param {bigint} w @param {number} n @returns {boolean} */
function lastGuard(u, w, n) {
  return 4n * (u + 3n) * (2n ** BigInt(n)) <= 2n * u + w + 3n * BigInt(n) + 9n;
}

/** @param {bigint} u @param {bigint} w @param {number} n @returns {boolean} */
function gateEquation(u, w, n) {
  return 2n * u + w + 3n * BigInt(n) + 13n === 4n * (u + 3n) * (2n ** BigInt(n));
}

let tested = 0;
let gateways = 0;
for (let u = 0n; u <= 48n; u++) {
  for (let w = 0n; w <= 400n; w++) {
    const end = burst(u, w);
    const k = end.steps;
    const expectedU = (u + 3n) * (2n ** BigInt(k)) - 3n;
    const expectedP = 2n * u + w + 3n * BigInt(k);
    assert.equal(end.u, expectedU);
    assert.equal(2n * end.u + end.w, expectedP);
    assert.equal(lastGuard(u, w, k), false);
    if (k > 0) assert.equal(lastGuard(u, w, k - 1), true);
    assert.equal(gateEquation(u, w, k), end.w + 1n === 2n * end.u);
    gateways += Number(end.w + 1n === 2n * end.u);
    tested++;
  }
}

let constructed = 0;
for (let u = 0n; u <= 80n; u++) {
  for (let n = 0; n <= 50; n++) {
    const w = 4n * (u + 3n) * (2n ** BigInt(n)) - 2n * u - 13n - 3n * BigInt(n);
    if (w < 0n) continue;
    const end = burst(u, w);
    assert.equal(end.steps, n);
    assert.equal(end.w + 1n, 2n * end.u);
    assert.equal(gateEquation(u, w, n), true);
    constructed++;
  }
}

let seed = 0x5edc1234n;
for (let i = 0; i < 100000; i++) {
  seed = (seed * 6364136223846793005n + 1442695040888963407n) & ((1n << 64n) - 1n);
  const u = seed & 0xffn;
  const w = seed >> 8n;
  const end = burst(u, w);
  assert.equal(lastGuard(u, w, end.steps), false);
  if (end.steps > 0) assert.equal(lastGuard(u, w, end.steps - 1), true);
  assert.equal(gateEquation(u, w, end.steps), end.w + 1n === 2n * end.u);
  tested++;
}

console.log(JSON.stringify({tested, constructed, gateways, verification: 'PASS'}));
