"use strict";

/**
 * Exact census of complete six-state, two-symbol 25-action tables with A/0=0RB
 * whose all-zero control flow cycles before any write-one or halting action.
 *
 * Only the 5 unassigned read-zero slots are enumerated; the 6 read-one slots
 * are unreachable on each certified cycle and contribute 25^6 free choices.
 * The 25 actions on every slot are: halt=0; zero-write actions=1..12;
 * one-write actions=13..24. Each zero-write successor has both directions.
 *
 * @returns {{total: number, cycleCount: number, byDistinctStates: number[]}}
 */
function exhaustiveCensus() {
  const pow25 = [1, 25, 625, 15625, 390625];
  const byDistinctStates = Array(7).fill(0);
  const total = 25 ** 5;

  for (let table = 0; table < total; table += 1) {
    let state = 1; // A's fixed 0RB leads to B (state 1)
    let seen = 0b000011; // initial A and B both visited
    let distinct = 2;

    for (;;) {
      const instruction = Math.floor(table / pow25[state - 1]) % 25;
      if (instruction === 0 || instruction >= 13) break;
      const next = (instruction - 1) % 6;
      if ((seen & (1 << next)) !== 0) {
        byDistinctStates[distinct] += 1;
        break;
      }
      seen |= 1 << next;
      distinct += 1;
      state = next;
    }
  }
  return {
    total,
    cycleCount: byDistinctStates.reduce((x, y) => x + y, 0),
    byDistinctStates
  };
}

/**
 * Independent symbolic count by first return to an already visited state.
 *
 * @returns {number[]}
 */
function firstRepeatFormula() {
  const count = Array(7).fill(0);
  let prefix = 1;
  for (let k = 2; k <= 6; k += 1) {
    count[k] = prefix * (2 * k) * 25 ** (6 - k);
    prefix *= 2 * (6 - k);
  }
  return count;
}

const checked = exhaustiveCensus();
const expected = firstRepeatFormula();
if (JSON.stringify(checked.byDistinctStates) !== JSON.stringify(expected)) {
  throw new Error(
    `Independent exhaustive and symbolic counts differ: ` +
    `${checked.byDistinctStates} versus ${expected}`
  );
}
if (checked.cycleCount !== 2605108 || checked.total !== 9765625) {
  throw new Error(`Unexpected census: ${JSON.stringify(checked)}`);
}

console.log("A/0=0RB: exact zero-writer closed-cycle count over 0-slots");
for (let k = 2; k <= 6; k += 1) {
  console.log(`Distinct visited states=${k}, tables=${checked.byDistinctStates[k]}`);
}
console.log(`Cycle-positive zero-slot tables = ${checked.cycleCount} / ${checked.total}`);
console.log(`Share of 0RB cylinder = ${(100 * checked.cycleCount / checked.total).toFixed(8)}%`);
console.log(`Complete machines classified = ${BigInt(checked.cycleCount) * 25n ** 6n}`);
console.log("Independently derived first-repeat formula matches exhaustive enumeration.");
