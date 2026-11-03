"use strict";

/** Independent finite checks of the new linear-time zero-mask witness against
 * the old exhaustive 64-bit-mask oracle. This test is computational evidence,
 * not a replacement for the Lean source proof of soundness.
 */
const STATE_COUNT = 6;
const SAMPLES = 250000;
let rng = 0x61e7cafe;

/** @returns {number} Uniform uint32 generated from a fixed seed. */
function random32() {
  rng = (Math.imul(rng, 1664525) + 1013904223) >>> 0;
  return rng;
}

/**
 * For the current zero-reading instruction:
 * -1 = unspecified, 0 = halt, 1..12 = zero-write ordinary,
 * 13..24 = one-write ordinary.
 * @param {readonly number[]} table
 * @param {number} mask
 * @returns {boolean}
 */
function maskGood(table, mask) {
  if ((mask & 1) === 0) return false;
  for (let state = 0; state < STATE_COUNT; state += 1) {
    if ((mask & (1 << state)) === 0) continue;
    const code = table[state];
    if (code < 1 || code > 12) return false;
    const next = (code - 1) % STATE_COUNT;
    if ((mask & (1 << next)) === 0) return false;
  }
  return true;
}

/** @param {readonly number[]} table
 *  @returns {boolean}
 */
function exhaustiveMask(table) {
  for (let mask = 1; mask < 64; mask += 2) {
    if (maskGood(table, mask)) return true;
  }
  return false;
}

/** @param {readonly number[]} table
 *  @returns {boolean}
 */
function pathMask(table) {
  let state = 0;
  let visited = 0;
  for (let step = 0; step <= STATE_COUNT; step += 1) {
    if ((visited & (1 << state)) !== 0) {
      return maskGood(table, visited);
    }
    visited |= 1 << state;
    const code = table[state];
    if (code < 1 || code > 12) return false;
    state = (code - 1) % STATE_COUNT;
  }
  return false;
}

let positiveFull0RB = 0;
let positivePartial = 0;
for (let i = 0; i < SAMPLES; i += 1) {
  const table = Array.from({length: STATE_COUNT}, (_, state) =>
    state === 0 ? 2 : random32() % 25);
  const old = exhaustiveMask(table);
  const next = pathMask(table);
  if (old !== next) {
    throw new Error(`Full-table discrepancy index ${i}: ${JSON.stringify(table)}`);
  }
  positiveFull0RB += Number(next);
}

for (let i = 0; i < SAMPLES; i += 1) {
  const table = Array.from({length: STATE_COUNT}, () =>
    (random32() % 29) - 4); // -4..-1 all model unspecified
  const old = exhaustiveMask(table);
  const next = pathMask(table);
  if (old !== next) {
    throw new Error(`Partial-table discrepancy index ${i}: ${JSON.stringify(table)}`);
  }
  positivePartial += Number(next);
}

console.log(`Cross-checked ${SAMPLES} complete 0RB zero-rows: ${positiveFull0RB} matches of both oracles`);
console.log(`Cross-checked ${SAMPLES} arbitrary partial zero-rows: ${positivePartial} matches of both oracles`);
console.log("No discrepancies between witnessed path-mask and 64-mask exhaustive oracle.");
