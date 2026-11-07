'use strict';

const fs = require('node:fs');
const path = require('node:path');

/** @typedef {{write: number, direction: number, next: number}} Action */

/** Parse a six-state two-symbol Busy Beaver RLE table. */
function parseMachine(rle) {
  const rows = rle.split('_');
  if (rows.length !== 6 || rows.some((row) => row.length !== 6)) {
    throw new Error(`Invalid machine: ${rle}`);
  }
  return rows.flatMap((row) => [row.slice(0, 3), row.slice(3, 6)].map((token) => {
    if (token === '---') return null;
    if (!/^[01][LR][A-F]$/.test(token)) throw new Error(`Invalid action: ${token}`);
    return { write: Number(token[0]), direction: token[1] === 'R' ? 1 : -1, next: token.charCodeAt(2) - 65 };
  }));
}

/**
 * Sound head-centered tape-window overapproximation retaining the saturated
 * distances to the two extrema ever scanned by the physical head.
 * An abstract possible halt is inconclusive, never an actual halt witness.
 * A complete finite abstract closure without possible halt is only a
 * candidate nonhalt certificate until the simulation relation is verified.
 *
 * @param {(Action|null)[]} rules
 * @param {number} radius
 * @param {number} cap Maximum queue capacity; exhaustion is inconclusive.
 * @param {Uint16Array} seen Reused visit tags indexed by encoded state.
 * @param {number} tag Unique tag for this machine.
 */
function checkMachine(rules, radius, cap, seen, tag) {
  const span = 2 ** (2 * radius + 1);
  const maskAll = span - 1;
  const center = 2 ** radius;
  const highBit = 2 ** (2 * radius);
  const dSize = radius + 2;
  const queue = new Uint32Array(cap);
  const depth = new Uint16Array(cap);
  let head = 0;
  let tail = 1;
  queue[0] = 0;
  seen[0] = tag;
  while (head < tail) {
    const id = queue[head];
    const distance = depth[head++];
    const left = id % dSize;
    const z0 = (id - left) / dSize;
    const right = z0 % dSize;
    const z1 = (z0 - right) / dSize;
    const bits = z1 % span;
    const control = (z1 - bits) / span;
    const read = (bits & center) === 0 ? 0 : 1;
    const action = rules[2 * control + read];
    if (action === null) return { status: 'abstract-halt', visited: head, generated: tail, depth: distance };

    const written = (bits & ~center) | (action.write ? center : 0);
    const shifted = action.direction === 1 ? written >>> 1 : (written << 1) & maskAll;
    const edgeBit = action.direction === 1 ? highBit : 1;
    const possibleRight = action.direction === 1 && right === radius + 1
      ? [radius, radius + 1]
      : [action.direction === 1 ? Math.max(0, right - 1) : Math.min(radius + 1, right + 1)];
    const possibleLeft = action.direction === -1 && left === radius + 1
      ? [radius, radius + 1]
      : [action.direction === -1 ? Math.max(0, left - 1) : Math.min(radius + 1, left + 1)];
    const incomingVisited = action.direction === 1 ? right > radius : left > radius;
    for (const r of possibleRight) {
      for (const l of possibleLeft) {
        for (let bit = 0; bit < (incomingVisited ? 2 : 1); bit++) {
          const newBits = shifted | (bit ? edgeBit : 0);
          const key = ((action.next * span + newBits) * dSize + r) * dSize + l;
          if (seen[key] === tag) continue;
          if (tail === cap) return { status: 'cap', visited: head, generated: tail };
          seen[key] = tag;
          queue[tail] = key;
          depth[tail++] = distance + 1;
        }
      }
    }
  }
  return { status: 'abstract-safe', visited: head, generated: tail };
}

function main() {
  const inputPath = path.resolve(process.argv[2] || 'resources/BB6_holdouts_663_2026-10-16.txt');
  const radius = Number(process.argv[3] || 7);
  const cap = Number(process.argv[4] || 400000);
  if (!Number.isInteger(radius) || radius < 0 || radius > 7) throw new Error('Radius must be between 0 and 7');
  if (!Number.isSafeInteger(cap) || cap <= 0) throw new Error('Cap must be a positive integer');
  const lines = fs.readFileSync(inputPath, 'utf8').trim().split(/\r?\n/);
  if (lines.length > 65534) throw new Error('At most 65534 machines per invocation');
  const span = 2 ** (2 * radius + 1);
  const seen = new Uint16Array(6 * span * (radius + 2) ** 2);
  const counts = { 'abstract-halt': 0, 'abstract-safe': 0, cap: 0 };
  let maxVisited = { visited: 0, name: null, depth: null };
  let minDepth = Infinity;
  let maxDepth = 0;
  for (let i = 0; i < lines.length; i++) {
    const result = checkMachine(parseMachine(lines[i]), radius, cap, seen, i + 1);
    counts[result.status]++;
    if (result.visited > maxVisited.visited) maxVisited = { visited: result.visited, name: lines[i], depth: result.depth ?? null };
    if (result.status === 'abstract-halt') {
      minDepth = Math.min(minDepth, result.depth);
      maxDepth = Math.max(maxDepth, result.depth);
    }
  }
  console.log(JSON.stringify({ radius, cap, inputCount: lines.length, counts, minDepth, maxDepth, maxVisited }, null, 2));
}

if (require.main === module) main();
module.exports = { parseMachine, checkMachine };
