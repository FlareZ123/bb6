#!/usr/bin/env node
"use strict";
/*
 * Exact arithmetic of SOURCE-DERIVED (not globally verified) Cryptid D
 * singleton-suffix normal forms.
 *
 * Q(n,t) = cfg_CR_n_n([(0,0)], rep(4*n+5,(0,0)) ++ [(0,0),(t,0)]).
 *
 * The shift Q(n,t+3)->Q(n+1,t) is kernel-checked against original source
 * in CI 45119240956. Residual zero Q(n,0)->D0(8n+15) and residual two
 * Q(n,2)->D0(8n+21) remain separate UNCOMPILED Lean draft theorems.
 *
 * Step counts are original source-clause sums (not counted Lean paths).
 * Do not treat output as a blank-root BB(6) proof or bound.
 */
function nat(s, name) {
  if (!/^\d+$/.test(s)) throw new Error(name + " must be a nonnegative integer");
  return BigInt(s);
}
function normalizeSingleton(n, t) {
  if (n < 0n || t < 0n) throw new RangeError("nonnegative n,t required");
  const rem = t % 3n;
  const k = (t - rem) / 3n;
  const m = n + k;
  const shiftOuter = 8n*n*k + 4n*k*k + 22n*k;
  const shiftRaw = 24n*n*k + 12n*k*k + 63n*k;
  if (rem === 1n) {
    return {
      source: {n: String(n), suffix: String(t)},
      shifts: String(k),
      terminal: {family: "Q", n: String(m), suffix: "1"},
      status: "residual-one-open",
      outer: String(shiftOuter),
      primitiveSteps: String(shiftRaw)
    };
  }
  const index = rem === 0n ? 8n*m + 15n : 8n*m + 21n;
  const baseOuter = rem === 0n ? 8n*m + 43n : 8n*m + 46n;
  const baseRaw = rem === 0n ? 16n*m + 109n : 40n*m + 196n;
  return {
    source: {n: String(n), suffix: String(t)},
    shifts: String(k),
    residual: String(rem),
    terminal: {family: "D0", parameter: String(index)},
    status: "conditional-source-normal-form",
    outer: String(shiftOuter + baseOuter),
    primitiveSteps: String(shiftRaw + baseRaw)
  };
}
function selfTest() {
  const checks = [
    [0n, 3n, "23", "200", "77"],
    [1n, 3n, "31", "240", "93"],
    [0n, 5n, "29", "311", "80"],
    [1n, 5n, "37", "375", "96"],
    [0n, 9n, "39", "454", "169"],
    [2n, 11n, "61", "837", "236"],
    [0n, 15n, "55", "804", "293"],
    [0n, 17n, "61", "1011", "296"]
  ];
  for (const [n, t, index, raw, outer] of checks) {
    const x = normalizeSingleton(n, t);
    if (x.terminal.parameter !== index ||
        x.primitiveSteps !== raw || x.outer !== outer)
      throw new Error("mismatch for " + n + "," + t + ": " + JSON.stringify(x));
  }
  const open = normalizeSingleton(4n, 7n);
  if (open.status !== "residual-one-open" ||
      open.terminal.n !== "6" || open.terminal.suffix !== "1")
    throw new Error("residual-one normal form mismatch");
  return "9 expected source-derived normal forms confirmed";
}
if (typeof module !== "undefined") module.exports = {normalizeSingleton, selfTest};
if (require.main === module) {
  if (process.argv.includes("--test")) {
    process.stdout.write(selfTest() + "\n");
  } else {
    if (process.argv.length !== 4)
      throw new Error("usage: node normalize.js <nonnegative n> <nonnegative suffix t>");
    process.stdout.write(JSON.stringify(
      normalizeSingleton(nat(process.argv[2], "n"), nat(process.argv[3], "t")),
      null, 2) + "\n");
  }
}
