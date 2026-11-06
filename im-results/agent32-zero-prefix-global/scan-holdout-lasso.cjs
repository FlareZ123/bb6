'use strict';

const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');

/** @typedef {{ write: number, direction: -1 | 1, next: number } | null} Action */
/** @typedef {{ state: number, head: number, ones: Set<number> }} Config */
/** @typedef {Action[][]} Machine */

/** @param {string} token @returns {Action} */
function parseAction(token) {
  if (token === '---') return null;
  const write = Number(token[0]);
  const direction = token[1] === 'R' ? 1 : token[1] === 'L' ? -1 : 0;
  const next = token.charCodeAt(2) - 65;
  if ((write !== 0 && write !== 1) || direction === 0 || next < 0 || next >= 6) {
    throw new Error(`Invalid transition token: ${token}`);
  }
  return { write, direction, next };
}

/** @param {string} rle @returns {Machine} */
function parseMachine(rle) {
  const rows = rle.trim().split('_');
  if (rows.length !== 6 || rows.some((row) => row.length !== 6)) {
    throw new Error(`Expected six six-character rows: ${rle}`);
  }
  return rows.map((row) => [parseAction(row.slice(0, 3)), parseAction(row.slice(3, 6))]);
}

/** @param {Machine} machine @param {Config} config @returns {boolean} */
function step(machine, config) {
  const action = machine[config.state][config.ones.has(config.head) ? 1 : 0];
  if (action === null) return false;
  if (action.write === 1) config.ones.add(config.head);
  else config.ones.delete(config.head);
  config.head += action.direction;
  config.state = action.next;
  return true;
}

/** @param {Config} config @returns {string} */
function configKey(config) {
  const ones = [...config.ones].sort((a, b) => a - b).join(',');
  return `${config.state}|${config.head}|${ones}`;
}

/** @param {Config} config @returns {boolean} */
function freshRight(config) {
  for (const x of config.ones) if (x >= config.head) return false;
  return true;
}

/** @param {Config} config @returns {boolean} */
function freshLeft(config) {
  for (const x of config.ones) if (x <= config.head) return false;
  return true;
}

/**
 * Compute same-state blank-tape right/left macros. Intermediate heads include
 * the initial position and exclude the final position, matching List.range n.
 * @param {Machine} machine
 * @param {number} macroLimit
 * @returns {{ right: number[][], left: number[][] }}
 */
function macroPatterns(machine, macroLimit) {
  const result = {
    right: Array.from({ length: 6 }, () => []),
    left: Array.from({ length: 6 }, () => []),
  };
  for (let startState = 0; startState < 6; startState += 1) {
    for (const direction of ['right', 'left']) {
      /** @type {Config} */
      const config = { state: startState, head: 0, ones: new Set() };
      /** @type {number[]} */
      const heads = [0];
      for (let n = 1; n <= macroLimit; n += 1) {
        if (!step(machine, config)) break;
        heads.push(config.head);
        if (config.state !== startState) continue;
        if (direction === 'right' && config.head > 0 && freshRight(config) && heads.slice(0, -1).every((x) => x >= 0)) {
          result.right[startState].push(n);
        }
        if (direction === 'left' && config.head < 0 && freshLeft(config) && heads.slice(0, -1).every((x) => x <= 0)) {
          result.left[startState].push(n);
        }
      }
    }
  }
  return result;
}

/**
 * Screen one full machine for an exact finite-configuration lasso or a
 * finite-entry fresh-ray macro.
 * @param {Machine} machine
 * @param {number} entryLimit
 * @param {number} macroLimit
 * @param {number} lassoLimit
 * @returns {null | { kind: 'exact-lasso', first: number, repeat: number, period: number } | { kind: 'entry-macro', entrySteps: number, state: number, head: number, direction: 'right' | 'left', macroSteps: number } | { kind: 'halts', steps: number }}
 */
function scanMachine(machine, entryLimit, macroLimit, lassoLimit) {
  const patterns = macroPatterns(machine, macroLimit);
  /** @type {Config} */
  const config = { state: 0, head: 0, ones: new Set() };
  const seen = new Map();
  const limit = Math.max(entryLimit, lassoLimit);

  for (let steps = 0; steps <= limit; steps += 1) {
    if (steps <= lassoLimit) {
      const key = configKey(config);
      if (seen.has(key)) {
        const first = seen.get(key);
        return { kind: 'exact-lasso', first, repeat: steps, period: steps - first };
      }
      seen.set(key, steps);
    }

    if (steps < entryLimit) {
      if (freshRight(config) && patterns.right[config.state].length > 0) {
        return {
          kind: 'entry-macro', entrySteps: steps, state: config.state,
          head: config.head, direction: 'right', macroSteps: patterns.right[config.state][0],
        };
      }
      if (freshLeft(config) && patterns.left[config.state].length > 0) {
        return {
          kind: 'entry-macro', entrySteps: steps, state: config.state,
          head: config.head, direction: 'left', macroSteps: patterns.left[config.state][0],
        };
      }
    }

    if (steps < limit && !step(machine, config)) return { kind: 'halts', steps };
  }
  return null;
}

function selfTest() {
  const readOneLasso = parseMachine('1RB0RB_0LA---_------_------_------_------');
  assert.deepEqual(scanMachine(readOneLasso, 10, 8, 12), {
    kind: 'exact-lasso', first: 0, repeat: 4, period: 4,
  });

  const entryToB = parseMachine('0RB---_1RC---_0LD---_---0RB_------_------');
  assert.deepEqual(scanMachine(entryToB, 2, 4, 12), {
    kind: 'entry-macro', entrySteps: 1, state: 1, head: 1,
    direction: 'right', macroSteps: 3,
  });

  const f287 = parseMachine('1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---');
  assert.equal(scanMachine(f287, 10000, 32, 1000), null);
  process.stdout.write('Self-tests passed: exact lasso, finite-entry macro, and F287 bounded negative screen.\n');
}

const args = process.argv.slice(2);
if (args[0] === '--self-test') {
  selfTest();
} else {
  const file = args[0] ?? path.resolve(__dirname, '../../resources/BB6_holdouts_663_2026-10-16.txt');
  const entryLimit = Number(args[1] ?? 10000);
  const macroLimit = Number(args[2] ?? 32);
  const lassoLimit = Number(args[3] ?? 1000);
  for (const [name, value] of Object.entries({ entryLimit, macroLimit, lassoLimit })) {
    if (!Number.isSafeInteger(value) || value < 0) throw new Error(`${name} must be a nonnegative safe integer`);
  }

  const lines = fs.readFileSync(file, 'utf8').split(/\r?\n/).map((line) => line.trim()).filter(Boolean);
  const hits = [];
  let halted = 0;
  for (let index = 0; index < lines.length; index += 1) {
    const result = scanMachine(parseMachine(lines[index]), entryLimit, macroLimit, lassoLimit);
    if (result === null) continue;
    if (result.kind === 'halts') halted += 1;
    else hits.push({ index: index + 1, rle: lines[index], ...result });
  }
  process.stdout.write(`${JSON.stringify({
    source: path.basename(file), machineCount: lines.length,
    limits: { entryLimit, macroLimit, lassoLimit },
    exactLassoCount: hits.filter((hit) => hit.kind === 'exact-lasso').length,
    entryMacroCount: hits.filter((hit) => hit.kind === 'entry-macro').length,
    haltedBeforeLimitCount: halted,
    hits,
  }, null, 2)}\n`);
}
