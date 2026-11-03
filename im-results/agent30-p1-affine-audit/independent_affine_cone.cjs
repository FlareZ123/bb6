"use strict";

/**
 * Independent read-only symbolic stress test of Agent 12's 187-residue P1
 * affine certificate. This is an experimental checker, not a replacement for
 * the source-connected Lean proof.
 *
 * Run with Node.js from any working directory. No packages required.
 */
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");

const aggregate = fs.readFileSync(
  path.join(__dirname, "..", "agent12-backwards", "P1RAffineAggregate.lean"),
  "utf8",
);
const match = aggregate.match(/def extraResidues[^\[]*\[([\s\S]*?)\]/);
assert(match, "Cannot locate Lean residue list");
const residues = match[1].split(",").map(value => BigInt(value.trim()));
assert.equal(residues.length, 187);

const zero = 0n;
const constant = value => [zero, value];
const plus = (a, b) => [a[0] + b[0], a[1] + b[1]];
const minus = (a, b) => [a[0] - b[0], a[1] - b[1]];
const times = (a, n) => [a[0] * n, a[1] * n];
const divide = (a, n) => {
  assert.equal(a[0] % n, 0n, "non-affine coefficient division");
  return [a[0] / n, a[1] / n];
};
const modular = (a, n, r) => a[0] % n === zero && a[1] % n === r;
const modLeaf = (b, d) =>
  modular(b, 4n, 2n) && b[1] > 2n && d[1] > zero;
const powerLeaf = (b, d) =>
  modular(b, 2n, zero) && modular(d, 2n, zero) &&
  d[1] > zero && b[0] >= 66048n && b[0] <= 130560n &&
  b[1] + 12n <= 129782n;

/** @param {bigint} value */
function valuationCut12(value) {
  let t = 0;
  while (t < 12 && value % 2n === zero) {
    value /= 2n;
    t++;
  }
  return t;
}

/** @param {bigint} residue */
function auditResidue(residue) {
  const outcome = {residue: Number(residue), hubs: 0, modLeaves: 0,
    powerLeaves: 0, maxDepth: 0};
  /** @param {bigint[]} b @param {bigint[]} d @param {number} fuel */
  function visit(b, d, fuel) {
    outcome.maxDepth = Math.max(outcome.maxDepth, 12 - fuel);
    if (modLeaf(b, d)) {
      outcome.modLeaves++;
      return;
    }
    if (powerLeaf(b, d)) {
      outcome.powerLeaves++;
      return;
    }
    assert(fuel > 0, "finite-cone fuel exhausted");
    assert(b[1] >= 8n && modular(b, 4n, zero) &&
      d[1] > zero, "nonterminal inverse hub is invalid");
    const cut = valuationCut12(d[1] + b[1] / 2n + 3n);
    const divisor = 2n ** BigInt(cut + 1);
    assert.equal((d[0] + b[0] / 2n) % divisor, zero);
    assert.notEqual((d[1] + b[1] / 2n + 3n) % divisor, zero);
    outcome.hubs++;

    let k = minus(divide(b, 4n), constant(1n));
    let c = plus(d, divide(b, 2n));
    for (let t = 0; t <= cut; t++) {
      if (t > 0) {
        assert(c[1] >= 3n && c[1] % 2n === 1n);
        c = divide(minus(c, constant(3n)), 2n);
        assert.equal(c[0] % 2n, zero, "non-affine floor division");
        k = plus(k, plus([c[0] / 2n, c[1] / 2n], constant(1n)));
      }
      assert(c[1] >= 2n && 2n * k[1] >= 4n);
      visit(minus(times(k, 2n), constant(4n)),
        plus(c, constant(4n)), fuel - 1);
    }
  }
  visit([131072n, 131072n - 2n * residue - 16n],
    constant(3n), 12);
  return outcome;
}

const outcomes = residues.map(auditResidue);
const source382 = outcomes.find(o => o.residue === 382);
assert.equal(source382.hubs, 31);
assert.equal(source382.modLeaves + source382.powerLeaves, 62);
assert.equal(new Set(residues.map(String)).size, 187);
assert(residues.every(r => r % 16n === 14n));
const totals = {
  families: outcomes.length,
  hubs: outcomes.reduce((s, o) => s + o.hubs, 0),
  modLeaves: outcomes.reduce((s, o) => s + o.modLeaves, 0),
  powerLeaves: outcomes.reduce((s, o) => s + o.powerLeaves, 0),
  maximumHubs: Math.max(...outcomes.map(o => o.hubs)),
  maximumDepth: Math.max(...outcomes.map(o => o.maxDepth)),
};
process.stdout.write(JSON.stringify(totals, null, 2) + "\n");
