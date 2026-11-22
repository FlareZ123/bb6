#!/usr/bin/env node
"use strict";

// Materialize exact per-edge S-window boundary data for the authentic
// D(0,7) recurrence. No external dependencies; run from the repository root.

const fs = require("node:fs");
const path = require("node:path");
const root = process.cwd();
const priorQ = JSON.parse(fs.readFileSync(
  path.join(root, "im-results/agent32-623-phase-automaton/ActualBoundaryPhases.json"),
  "utf8"
));

const floorDiv = (a, b) => {
  let q = a / b;
  const r = a % b;
  if (r !== 0n && a < 0n) q -= 1n;
  return q;
};
const mod = (a, b) => {
  let r = a % b;
  if (r < 0n) r += b;
  return r;
};
const pow3 = k => 3n ** BigInt(k);

function evalA(a, k, m) {
  for (;;) {
    const q = k / 3n;
    const r = k % 3n;
    if (r === 2n) return [a + 1n, q, m];
    if (a === 0n) return r === 0n ? null : [0n, q, m];
    if (r === 0n) return [a - 1n, q, m + 2n];
    a -= 1n;
    m += 2n * q + 3n;
    k = q;
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
  const next = evalA(d + 1n - a, a, 2n * a + 5n);
  return next === null ? null : drainB(...next);
}

function sectorData(a, d) {
  let q, p, sector;
  if (a >= d) {
    q = d; p = a - d; sector = d % 2n === 1n ? "LO" : "LE";
  } else {
    q = a; p = d - a; sector = d % 2n === 1n ? "RO" : "RE";
  }
  const g = p - 3n * q;
  const S = a + d;
  const gamma = { LO: 18n, LE: 10n, RO: 2n, RE: 4n }[sector];
  return { q, g, S, x: 2n * g - gamma, y: 6n * q, sector };
}

function ellOf(v) {
  let ell = 0;
  let power = 1n;
  while ((power - 1n) / 2n < v + 3n) {
    ell += 1;
    power *= 3n;
  }
  return ell;
}

function windowIndices(B) {
  let k = 0;
  let p = 1;
  while (p <= B) { p *= 3; k += 1; }
  let j = 0;
  let p3 = 1n;
  const target = BigInt(B) ** 3n;
  while (p3 <= target) { p3 *= 3n; j += 1; }
  return { k, j };
}

function digitAt(x, i) {
  return Number(mod(floorDiv(x, pow3(i)), 3n));
}

function drainStats(b) {
  const value = 2n * b - 1n;
  let L = b % 2n === 1n ? 1 : 2;
  let p = pow3(L + 1);
  while (p <= value) { L += 2; p *= 9n; }
  const N = (value + pow3(L)) / 4n;
  let z = N;
  let n1 = 0;
  let n2 = 0;
  while (z > 0n) {
    const digit = z % 3n;
    if (digit === 1n) n1 += 1;
    if (digit === 2n) n2 += 1;
    z /= 3n;
  }
  return { L, n1, n2, D: L - 2 * n2, R: n1 + n2 };
}

const correctionConstants = {
  "LO/L": [-122n, 84n], "LE/L": [-68n, 48n],
  "RO/L": [0n, 0n], "RE/L": [-36n, 18n],
  "LO/R": [-6n, 24n], "LE/R": [-12n, 18n],
  "RO/R": [-44n, 30n], "RE/R": [-20n, 18n],
};

function corrections(sector, branch, stats) {
  const [cC, cF] = correctionConstants[sector + "/" + branch];
  if (branch === "L") return {
    C: -18n * BigInt(stats.L) - 16n * BigInt(stats.n1) + 20n * BigInt(stats.n2) + cC,
    F: 12n * BigInt(stats.L) + 12n * BigInt(stats.n1) - 12n * BigInt(stats.n2) + cF,
  };
  return {
    C: 12n * BigInt(stats.L) + 4n * BigInt(stats.n1) - 20n * BigInt(stats.n2) + cC,
    F: -6n * BigInt(stats.L) + 12n * BigInt(stats.n2) + cF,
  };
}

function sourceCarry(source, branch, C, F, k) {
  const K = pow3(k);
  const K1 = pow3(k + 1);
  const xK1 = mod(source.x, K1);
  const xK = mod(source.x, K);
  const yK = mod(source.y, K);
  if (branch === "L") {
    return [
      floorDiv(xK1 - 3n * yK + C, K1),
      floorDiv(3n * yK + F, K1),
    ];
  }
  return [
    floorDiv(-xK1 - 3n * xK - 3n * yK + C, K1),
    floorDiv(3n * xK + 3n * yK + F, K1),
  ];
}

function emit(source, branch, carry, prev, i) {
  const xi = BigInt(digitAt(source.x, i));
  const yi = BigInt(digitAt(source.y, i));
  let tx, ty;
  if (branch === "L") {
    tx = xi - BigInt(prev[1]) + carry[0];
    ty = BigInt(prev[1]) + carry[1];
  } else {
    tx = -xi - BigInt(prev[0]) - BigInt(prev[1]) + carry[0];
    ty = BigInt(prev[0]) + BigInt(prev[1]) + carry[1];
  }
  return {
    input: [Number(xi), Number(yi)],
    output: [Number(mod(tx, 3n)), Number(mod(ty, 3n))],
    carryIn: carry.map(Number),
    carryOut: [Number(floorDiv(tx, 3n)), Number(floorDiv(ty, 3n))],
    prevIn: prev.slice(),
    carryBig: [floorDiv(tx, 3n), floorDiv(ty, 3n)],
    prevOut: [Number(xi), Number(yi)],
  };
}

function qWindowPhase(source, branch, C, F) {
  const ell = ellOf(source.q);
  const B = Math.max(34 * ell + 122, 36 * ell + 88);
  const { k } = windowIndices(B);
  const carry = sourceCarry(source, branch, C, F, k);
  const prev = [digitAt(source.x, k), digitAt(source.y, k)];
  return [source.sector, branch, prev.join(","), carry.map(Number).join(",")].join("|");
}

function transition(source, target) {
  const sourceEll = ellOf(source.S);
  const targetEll = ellOf(target.S);
  const sourceWindow = windowIndices(34 * sourceEll + 122);
  const targetWindow = windowIndices(34 * targetEll + 122);
  const branch = source.g > 0n ? "L" : "R";
  const drainInput = source.q + ({ LO: 3n, LE: 2n, RO: -1n, RE: 1n }[source.sector]);
  const stats = drainStats(drainInput);
  const { C, F } = corrections(source.sector, branch, stats);
  const T = 3n * BigInt(stats.D) + 2n * BigInt(stats.R) +
    ({ LO: 19n, LE: 10n, RO: -4n, RE: 2n }[source.sector]);

  let carry = sourceCarry(source, branch, C, F, sourceWindow.k);
  let prev = [digitAt(source.x, sourceWindow.k), digitAt(source.y, sourceWindow.k)];
  const lowBoundary = [];
  for (let i = sourceWindow.k + 1; i <= targetWindow.k + 1; i += 1) {
    const step = emit(source, branch, carry, prev, i);
    lowBoundary.push(step);
    carry = step.carryBig;
    prev = step.prevOut;
  }

  const kShift = targetWindow.k - sourceWindow.k;
  const jShift = targetWindow.j - sourceWindow.j;
  const sourceR = sourceWindow.j - 3 * sourceWindow.k;
  const targetR = targetWindow.j - 3 * targetWindow.k;
  if (![0, 1].includes(kShift) || ![0, 1].includes(jShift) ||
      (kShift === 1 && jShift !== 1)) {
    throw new Error("invalid S-window shift");
  }
  if (![-2, -1, 0].includes(sourceR) || ![-2, -1, 0].includes(targetR)) {
    throw new Error("invalid S-window boundary residue");
  }

  let lowExtension = null;
  let highExtension = null;
  let verifyCarry = carry;
  let verifyPrev = prev;
  let mismatches = 0;
  for (let i = targetWindow.k + 2; i < targetWindow.j - 2; i += 1) {
    const step = emit(source, branch, verifyCarry, verifyPrev, i);
    if (step.output[0] !== digitAt(target.x, i) ||
        step.output[1] !== digitAt(target.y, i)) mismatches += 1;
    if (kShift === 0 && i === targetWindow.k + 2) lowExtension = step;
    if (jShift === 1 && i === sourceWindow.j - 2) highExtension = step;
    verifyCarry = step.carryBig;
    verifyPrev = step.prevOut;
  }

  const boundaryCarry = [Number(carry[0]), Number(carry[1])];
  const key = [
    source.sector, branch, target.sector, target.g > 0n ? "L" : "R",
    prev.join(","), boundaryCarry.join(","), sourceR, targetR, kShift, jShift,
  ].join("|");
  const core = [
    source.sector, branch, target.sector, target.g > 0n ? "L" : "R",
    prev[0], prev[1], boundaryCarry[0], boundaryCarry[1],
    sourceR, targetR, kShift, jShift,
  ];
  const edge = [
    sourceWindow.k, sourceWindow.j, targetWindow.k, targetWindow.j,
    stats.L, stats.n1, stats.n2, stats.D, stats.R,
  ];
  const pairCode = pair => 3 * pair[0] + pair[1];
  return {
    key, core, edge,
    lowBoundaryCodes: lowBoundary.map(step => pairCode(step.output)),
    lowExtension: lowExtension === null ? null : [
      pairCode(lowExtension.input), pairCode(lowExtension.output),
      ...lowExtension.carryIn, ...lowExtension.carryOut, ...lowExtension.prevIn,
    ],
    highExtension: highExtension === null ? null : [
      pairCode(highExtension.input), pairCode(highExtension.output),
      ...highExtension.carryIn, ...highExtension.carryOut, ...highExtension.prevIn,
    ],
    mismatches,
    branch,
    branchByThreshold: source.g >= T ? "L" : "R",
    C, F,
    stats,
  };
}

function collect() {
  const priorSet = new Set(priorQ.phases.map(p =>
    [p.sector, p.branch, p.prev.join(","), p.carry.join(",")].join("|")
  ));
  const qSet = new Set();
  const phaseIds = new Map();
  const phaseRecords = [];
  const edges = [];
  const shiftHistogram = {};
  let a = 0n;
  let d = 7n;
  let branchMismatches = 0;
  let carryRectangleViolations = 0;
  let affineUpdateMismatches = 0;
  let transducerDigitMismatches = 0;
  let lowExtensionCount = 0;
  let highExtensionCount = 0;
  let transitionsChecked = 0;

  for (let n = 0; n <= 10000; n += 1) {
    const next = highLevelNext(a, d);
    if (n >= 33 && next !== null) {
      const source = sectorData(a, d);
      const target = sectorData(next[0], next[1]);
      const branch = source.g > 0n ? "L" : "R";
      const drainInput = source.q + ({ LO: 3n, LE: 2n, RO: -1n, RE: 1n }[source.sector]);
      const stats = drainStats(drainInput);
      const { C, F } = corrections(source.sector, branch, stats);
      qSet.add(qWindowPhase(source, branch, C, F));

      const result = transition(source, target);
      if (result.branchByThreshold !== branch) branchMismatches += 1;
      const [ca, cb] = result.core.slice(6, 8);
      if (branch === "L") {
        if (ca < -2 || ca > 2 || cb < -2 || cb > 2) carryRectangleViolations += 1;
      } else {
        if (ca < -4 || ca > 1 || cb < -2 || cb > 2) carryRectangleViolations += 1;
      }
      const outX = branch === "L"
        ? source.x - 3n * source.y + result.C
        : -4n * source.x - 3n * source.y + result.C;
      const outY = branch === "L"
        ? 3n * source.y + result.F
        : 3n * source.x + 3n * source.y + result.F;
      if (outX !== target.x || outY !== target.y) affineUpdateMismatches += 1;
      transducerDigitMismatches += result.mismatches;

      let phaseId = phaseIds.get(result.key);
      if (phaseId === undefined) {
        phaseId = phaseIds.size;
        phaseIds.set(result.key, phaseId);
        phaseRecords.push([phaseId, result.key, result.core]);
      }
      if (result.lowExtension !== null) lowExtensionCount += 1;
      if (result.highExtension !== null) highExtensionCount += 1;
      edges.push([
        n + 1, phaseId, ...result.edge,
        result.lowBoundaryCodes, result.lowExtension, result.highExtension,
      ]);
      const shift = result.core[10] + "," + result.core[11];
      shiftHistogram[shift] = (shiftHistogram[shift] || 0) + 1;
      transitionsChecked += 1;
    }

    if (n === 10000) break;
    if (next === null) break;
    [a, d] = next;
  }

  const qWindowPhaseSetMatchesExisting = priorSet.size === qSet.size &&
    [...priorSet].every(key => qSet.has(key));
  if (!qWindowPhaseSetMatchesExisting || branchMismatches ||
      carryRectangleViolations || affineUpdateMismatches || transducerDigitMismatches) {
    throw new Error("one or more S-window source checks failed");
  }

  const output = {
    title: "Machine #623 source-faithful S-window edge phases and exact extensions",
    evidenceType: "finite recurrence diagnostic; exact per-edge data, not an all-time invariant",
    sourceTransitionIndices: [33, 10000],
    targetStateIndices: [34, 10001],
    windowConvention: {
      buffer: "B=34*ellS+122",
      ellS: "least ell with (3^ell-1)/2 >= S+3, S=a+d",
      sourceWindow: "[kS+2,jS-2)",
      targetWindow: "[kS'+2,jS'-2)",
      oldOutputOverlap: "[kS+3,jS-2)",
      shifts: "(kS'-kS,jS'-jS) in {(0,0),(0,1),(1,1)}",
      lowExtension: "if kShift=0, target adds output at kS+2 before old-output overlap",
      highExtension: "if jShift=1, target adds output at jS-2 after old-output overlap",
      boundaryState: "(previous source digit pair, carry pair) entering target digit kS'+2 after consuming source digits kS+1,...,kS'+1",
    },
    validation: {
      transitionsChecked,
      qWindowPhaseSetMatchesExisting,
      qWindowUniquePhases: qSet.size,
      branchSelectionMismatches: branchMismatches,
      carryRectangleViolations: carryRectangleViolations,
      affineUpdateMismatches,
      transducerDigitMismatches,
      lowExtensionCount,
      highExtensionCount,
      shiftHistogram,
    },
    phaseRecordEncoding: [
      "id", "key",
      "[sourceSector,sourceBranch,targetSector,targetBranch,prevX,prevY,carryX,carryY,sourceR,targetR,kShift,jShift]",
    ],
    edgeEncoding: [
      "targetIndex", "phaseId",
      "sourceK", "sourceJ", "targetK", "targetJ",
      "drainLength", "n1", "n2", "D", "R",
      "lowBoundaryOutputPairCodes",
      "lowExtension:[inputPairCode,outputPairCode,carryInX,carryInY,carryOutX,carryOutY,prevInX,prevInY] or null",
      "highExtension:[inputPairCode,outputPairCode,carryInX,carryInY,carryOutX,carryOutY,prevInX,prevInY] or null",
    ],
    phaseRecords,
    edges,
  };

  const outputPath = path.join(root, "im-results/agent48-623-tight-window/SWindowEdgeRecords.json");
  fs.writeFileSync(outputPath, JSON.stringify(output) + "\n");
  console.log(JSON.stringify(output.validation, null, 2));
}

collect();
