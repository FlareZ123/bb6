#!/usr/bin/env node
"use strict";

// Reproduce the finite audit in SectorNormalizedLowDigitCocycle.md.
// Run from the repository root:
//   node im-results/agent27-623-root-scan/verify_sector_normalized_cocycle.js
//
// This checks the 9,968 materialized S-window edges. It is a finite
// source-recurrence diagnostic, not an all-time root invariant.

const fs = require("node:fs");
const path = require("node:path");
const assert = require("node:assert/strict");

const edgePath = path.join(
  process.cwd(),
  "im-results/agent48-623-tight-window/SWindowEdgeRecords.json"
);
const edgeData = JSON.parse(fs.readFileSync(edgePath, "utf8"));
const phaseById = new Map(
  edgeData.phaseRecords.map(([id, _key, phase]) => [id, phase])
);

function mod3(x) {
  const r = x % 3n;
  return r < 0n ? r + 3n : r;
}

function evalA(a, k, m) {
  for (;;) {
    if (k % 3n === 2n) return [a + 1n, k / 3n, m];
    if (a === 0n) return k % 3n === 0n ? null : [0n, k / 3n, m];
    if (k % 3n === 0n) return [a - 1n, k / 3n, m + 2n];
    k /= 3n;
    m += 2n * k + 3n;
    a -= 1n;
  }
}

function drainB(a, b, d) {
  while (b !== 0n) {
    const next = evalA(a, b - 1n, d + 2n * b + 3n);
    if (next === null || next[1] >= b) return null;
    [a, b, d] = next;
  }
  return [a, d];
}

function highLevelNext(a, d) {
  if (a === 0n) return d % 2n === 1n ? drainB(d + 1n, 2n, 2n) : [d, 7n];
  if (d % 2n === 1n && a >= d + 5n) return drainB(a - d - 5n, d + 3n, 5n);
  if (d % 2n === 0n && a >= d + 3n) return drainB(a - d - 2n, d + 2n, 2n);
  if (a % 2n === 1n) return null;
  if (a === d + 2n) return drainB(0n, a, 2n);
  if (d % 2n === 1n) return drainB(d + 4n - a, a - 1n, 3n);
  const first = evalA(d + 1n - a, a, 2n * a + 5n);
  return first === null ? null : drainB(...first);
}

function sectorData(a, d) {
  let q, p, sector;
  if (a >= d) {
    q = d;
    p = a - d;
    sector = d % 2n === 1n ? "LO" : "LE";
  } else {
    q = a;
    p = d - a;
    sector = d % 2n === 1n ? "RO" : "RE";
  }
  return { q, p, g: p - 3n * q, sector };
}

const betaConstant = { LO: -5n, LE: -2n, RO: 4n, RE: 1n };
const deltaConstant = { LO: 14n, LE: 8n, RO: 0n, RE: 3n };
// Agent 48 stores full evaluator-call R. In RE, Agent 1's r=R-1.
const thresholdConstant = { LO: 19n, LE: 10n, RO: -4n, RE: 2n };
const eta = { LO: 0n, LE: 0n, RO: 1n, RE: 0n };

let a = 0n;
let d = 7n;
for (let n = 0; n < 33; n += 1) {
  const next = highLevelNext(a, d);
  assert.notEqual(next, null, "blank-root prefix halted before D33");
  [a, d] = next;
}

let checked = 0;
const keys = new Set();

for (const row of edgeData.edges) {
  const targetIndex = row[0];
  const phaseId = row[1];
  const drainLength = row[6];
  const n1 = row[7];
  const n2 = row[8];
  const D = BigInt(row[9]);
  const fullR = BigInt(row[10]);
  const phase = phaseById.get(phaseId);
  assert.ok(phase, "missing phase record");
  const [sourceSector, branch, targetSector, targetBranch] = phase;

  const source = sectorData(a, d);
  assert.equal(source.sector, sourceSector, "source sector mismatch");
  assert.equal(source.g > 0n ? "L" : "R", branch, "source branch mismatch");

  const beta = -D + betaConstant[sourceSector];
  const delta = 2n * D + 2n * fullR + deltaConstant[sourceSector];
  const threshold = 3n * D + 2n * fullR + thresholdConstant[sourceSector];

  let pNext, qNext;
  if (branch === "L") {
    pNext = source.p - 3n * source.q - threshold;
    qNext = 3n * source.q + delta;
  } else {
    pNext = 3n * source.q + threshold - source.p;
    qNext = source.p + beta;
  }
  assert.ok(pNext >= 0n && qNext >= 0n, "negative canonical successor");

  const aNext = branch === "L" ? qNext + pNext : qNext;
  const dNext = branch === "L" ? qNext : qNext + pNext;
  const target = sectorData(aNext, dNext);
  assert.equal(target.sector, targetSector, "target sector mismatch");
  assert.equal(target.g > 0n ? "L" : "R", targetBranch, "target branch mismatch");

  const r = fullR - (sourceSector === "RE" ? 1n : 0n);
  const WHat = mod3(2n * source.p + eta[sourceSector]);
  const WHatNext = mod3(2n * pNext + eta[targetSector]);

  const activePredicted =
    branch === "L"
      ? D + r + 1n - (sourceSector === "RO" ? 1n : 0n)
      : WHat + D + 2n - (sourceSector === "RO" ? 1n : 0n);
  const passivePredicted =
    branch === "L"
      ? WHat - r + 1n
      : -WHat + r + 2n *
          (sourceSector === "LE" || sourceSector === "RO" ? 1n : 0n);

  const activeActual =
    branch === "L"
      ? 6n * source.q + 2n * delta
      : 2n * source.p + 2n * beta;

  assert.equal(
    mod3(activePredicted),
    mod3(activeActual),
    "active quotient mod-3 mismatch"
  );
  assert.equal(
    mod3(passivePredicted),
    WHatNext,
    "normalized passive quotient mod-3 mismatch"
  );

  keys.add([
    sourceSector,
    branch,
    mod3(D).toString(),
    mod3(r).toString(),
    WHat.toString(),
  ].join("|"));

  // Retain references to the fields that define this finite audit row.
  assert.ok(drainLength >= 0 && n1 >= 0 && n2 >= 0);
  [a, d] = [aNext, dNext];
  checked += 1;
  assert.equal(targetIndex, 33 + checked);
}

assert.equal(checked, 9968);
assert.equal(keys.size, 216);

process.stdout.write(JSON.stringify({
  checked,
  distinctNormalizedResidueStates: keys.size,
  sourceAndTargetPhaseMismatches: 0,
  activeMod3Mismatches: 0,
  passiveMod3Mismatches: 0,
  interpretation: "finite edge audit only; not an all-time invariant"
}, null, 2) + "\n");
