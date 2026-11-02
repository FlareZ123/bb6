'use strict';

/**
 * Count canonical n-state, two-symbol transition tables with a blank-origin
 * path that moves strictly in one fixed direction forever.
 * Every ordinary instruction has n next-state, two write, two direction
 * choices. Halting instructions collapse to one canonical choice.
 * No files are read or written.
 */

/** @param {number} n @returns {bigint} */
function powerChoices(states, exponent) {
  return BigInt(4 * states + 1) ** BigInt(exponent);
}

/** @param {number} mask @returns {number} */
function popcount(mask) {
  let count = 0;
  while (mask !== 0) {
    mask &= mask - 1;
    count++;
  }
  return count;
}

/**
 * Independent memoized exhaustive orbit-count recurrence.
 * If next state was seen, all unvisited zero-reading transitions are free.
 * @param {number} states
 * @returns {bigint}
 */
function countRayZeroDP(states) {
  /** @type {Map<string,bigint>} */
  const memo = new Map();

  /** @param {number} state @param {number} visited @returns {bigint} */
  function visit(state, visited) {
    if ((visited & (1 << state)) !== 0) {
      return powerChoices(states, states - popcount(visited));
    }
    const key = `${state}:${visited}`;
    const existing = memo.get(key);
    if (existing !== undefined) return existing;

    const newVisited = visited | (1 << state);
    let total = 0n;
    for (let next = 0; next < states; next++) {
      total += 2n * visit(next, newVisited);
    }
    memo.set(key, total);
    return total;
  }
  return visit(0, 0);
}

/**
 * Independent first-repetition count: after k distinct states there are
 * (n-1)_(k-1) possible paths, k return targets, 2^k write choices,
 * and 25^(n-k) arbitrary unvisited zero-reading entries.
 * @param {number} states
 * @returns {bigint}
 */
function countRayZeroFormula(states) {
  let count = 0n;
  for (let k = 1; k <= states; k++) {
    let falling = 1n;
    for (let j = 1; j < k; j++) falling *= BigInt(states - j);
    count += falling * BigInt(k) * (2n ** BigInt(k)) * powerChoices(states, states - k);
  }
  return count;
}

for (let n = 1; n <= 6; n++) {
  const dp = countRayZeroDP(n);
  const formula = countRayZeroFormula(n);
  if (dp !== formula) {
    throw new Error(`Independent methods disagree for ${n} states`);
  }

  const perDirection = dp * powerChoices(n, n);
  const bothDirections = 2n * perDirection;
  const total = powerChoices(n, 2 * n);
  // Directions disjoint: the initial A0 instruction cannot be both R and L.
  if (bothDirections > total) throw new Error('Unphysical count');
  const partsPerMillion = bothDirections * 1000000n / total;
  process.stdout.write(
    `states=${n} zero_tables_per_direction=${dp} ` +
    `full_tables_both_directions=${bothDirections} ` +
    `total_full_tables=${total} ppm=${partsPerMillion}\n`,
  );
}

module.exports = { countRayZeroDP, countRayZeroFormula };
