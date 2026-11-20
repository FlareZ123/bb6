#!/usr/bin/env node
// Compute the actual S-indexed boundary phase for the #623 reset window.
// The S-window word begins at k_S+2, so this advances the source transducer
// through the low input digit k_S+1 before recording the start phase.
// It also recomputes the older q-window phases and checks them against
// ActualBoundaryPhases.json as a validation of the affine/carry formulas.

const fs = require("node:fs");
const path = require("node:path");
const root = process.cwd();
const priorPath = path.join(root, "im-results/agent32-623-phase-automaton/ActualBoundaryPhases.json");
const prior = JSON.parse(fs.readFileSync(priorPath, "utf8"));

function evalA(a, k, m) {
  while (true) {
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
  const p = evalA(d + 1n - a, a, 2n * a + 5n);
  return p === null ? null : drainB(...p);
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
  const g = p - 3n * q;
  const gamma = { LO: 18n, LE: 10n, RO: 2n, RE: 4n }[sector];
  return { q, S: a + d, g, gamma, x: 2n * g - gamma, y: 6n * q, sector };
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

function floorDiv(a, b) {
  let q = a / b;
  const r = a % b;
  if (r !== 0n && a < 0n) q -= 1n;
  return q;
}

function mod(a, b) {
  let r = a % b;
  if (r < 0n) r += b;
  return r;
}

function pow3(k) {
  return 3n ** BigInt(k);
}

function windowIndices(B) {
  let k = 0;
  let p = 1;
  while (p <= B) {
    p *= 3;
    k += 1;
  }
  let j = 0;
  let p3 = 1n;
  const target = BigInt(B) ** 3n;
  while (p3 <= target) {
    p3 *= 3n;
    j += 1;
  }
  return { k, j };
}

function drainStats(b) {
  const value = 2n * b - 1n;
  let L = b % 2n === 1n ? 1 : 2;
  let p = pow3(L + 1);
  while (p <= value) {
    L += 2;
    p *= 9n;
  }
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
  return { L, N, n1, n2, D: L - 2 * n2, R: n1 + n2 };
}

const correctionConstants = {
  "LO/L": [-122n, 84n],
  "LE/L": [-68n, 48n],
  "RO/L": [0n, 0n],
  "RE/L": [-36n, 18n],
  "LO/R": [-6n, 24n],
  "LE/R": [-12n, 18n],
  "RO/R": [-44n, 30n],
  "RE/R": [-20n, 18n],
};

function corrections(sector, branch, stats) {
  const [cC, cF] = correctionConstants[sector + "/" + branch];
  if (branch === "L") {
    return {
      C: -18n * BigInt(stats.L) - 16n * BigInt(stats.n1) + 20n * BigInt(stats.n2) + cC,
      F: 12n * BigInt(stats.L) + 12n * BigInt(stats.n1) - 12n * BigInt(stats.n2) + cF,
    };
  }
  return {
    C: 12n * BigInt(stats.L) + 4n * BigInt(stats.n1) - 20n * BigInt(stats.n2) + cC,
    F: -6n * BigInt(stats.L) + 12n * BigInt(stats.n2) + cF,
  };
}

function phaseAtWindow(a, d, mode) {
  const sd = sectorData(a, d);
  const ell = mode === "q" ? ellOf(sd.q) : ellOf(sd.S);
  const B = mode === "q" ? Math.max(34 * ell + 122, 36 * ell + 88) : 34 * ell + 122;
  const { k, j } = windowIndices(B);
  const K = pow3(k);
  const K1 = pow3(k + 1);
  const branch = sd.g > 0n ? "L" : "R";
  const drainInput = sd.q + ({ LO: 3n, LE: 2n, RO: -1n, RE: 1n }[sd.sector]);
  const stats = drainStats(drainInput);
  const { C, F } = corrections(sd.sector, branch, stats);
  const T = 3n * BigInt(stats.D) + 2n * BigInt(stats.R) +
    ({ LO: 19n, LE: 10n, RO: -4n, RE: 2n }[sd.sector]);
  const branchByThreshold = sd.g >= T ? "L" : "R";

  const xK1 = mod(sd.x, K1);
  const xK = mod(sd.x, K);
  const yK = mod(sd.y, K);
  let carryA;
  let carryB;
  if (branch === "L") {
    carryA = floorDiv(xK1 - 3n * yK + C, K1);
    carryB = floorDiv(3n * yK + F, K1);
  } else {
    carryA = floorDiv(-xK1 - 3n * xK - 3n * yK + C, K1);
    carryB = floorDiv(3n * xK + 3n * yK + F, K1);
  }

  const prev = [
    Number(mod(floorDiv(sd.x, K), 3n)),
    Number(mod(floorDiv(sd.y, K), 3n)),
  ];
  const base = {
    sector: sd.sector,
    branch,
    k,
    j,
    ell,
    B,
    r: j - 3 * k,
    prev,
    carry: [Number(carryA), Number(carryB)],
    drainInput: drainInput.toString(),
    drainLength: stats.L,
    n1: stats.n1,
    n2: stats.n2,
    D: stats.D,
    R: stats.R,
    C: C.toString(),
    F: F.toString(),
    x: sd.x.toString(),
    y: sd.y.toString(),
    g: sd.g.toString(),
    T: T.toString(),
    branchByThreshold,
  };

  if (mode === "q") return base;

  // S-window starts at k+2, unlike the q-window at k+1.
  // Consume the low input pair at k+1 to obtain the phase entering k+2.
  const xK1Digit = Number(mod(floorDiv(sd.x, K1), 3n));
  const yK1Digit = Number(mod(floorDiv(sd.y, K1), 3n));
  let tx;
  let ty;
  if (branch === "L") {
    tx = BigInt(xK1Digit) - BigInt(prev[1]) + carryA;
    ty = BigInt(prev[1]) + carryB;
  } else {
    tx = -BigInt(xK1Digit) - BigInt(prev[0]) - BigInt(prev[1]) + carryA;
    ty = BigInt(prev[0]) + BigInt(prev[1]) + carryB;
  }
  base.phaseAtK2 = {
    prev: [xK1Digit, yK1Digit],
    carry: [Number(floorDiv(tx, 3n)), Number(floorDiv(ty, 3n))],
    lowOutput: [Number(mod(tx, 3n)), Number(mod(ty, 3n))],
  };
  return base;
}

function qKey(p) {
  return [p.sector, p.branch, p.prev.join(","), p.carry.join(",")].join("|");
}

function sKey(p) {
  return [p.sector, p.branch, p.phaseAtK2.prev.join(","), p.phaseAtK2.carry.join(","), p.r].join("|");
}

function increment(map, key) {
  map[key] = (map[key] || 0) + 1;
}

function collect() {
  let a = 0n;
  let d = 7n;
  const qPhases = new Set();
  const sPhases = new Map();
  const phaseTransitions = new Map();
  const qBranchCounts = { L: 0, R: 0 };
  const sBranchCounts = { L: 0, R: 0 };
  const qPrevCarry = { L: new Set(), R: new Set() };
  const sPrevCarry = { L: new Set(), R: new Set() };
  const sCarryPairs = { L: new Set(), R: new Set() };
  const sSectorBranchCounts = {};
  const sRHistogram = {};
  const sShiftHistogram = {};
  const sRTransitionHistogram = {};
  let branchMismatches = 0;
  let carryRectViolations = 0;
  let affineUpdateMismatches = 0;
  let index38 = null;
  let rootStates = 0;
  let transitions = 0;

  for (let n = 0; n <= 10000; n += 1) {
    let qPhase = null;
    let sPhase = null;
    if (n >= 33) {
      qPhase = phaseAtWindow(a, d, "q");
      sPhase = phaseAtWindow(a, d, "S");
      qPhases.add(qKey(qPhase));
      qBranchCounts[qPhase.branch] += 1;
      qPrevCarry[qPhase.branch].add(qPhase.prev.join(",") + "/" + qPhase.carry.join(","));

      const sk = sKey(sPhase);
      if (!sPhases.has(sk)) {
        sPhases.set(sk, { key: sk, count: 0, firstIndex: n, phase: {
          sector: sPhase.sector,
          branch: sPhase.branch,
          prev: sPhase.phaseAtK2.prev,
          carry: sPhase.phaseAtK2.carry,
          r: sPhase.r,
        }});
      }
      sPhases.get(sk).count += 1;
      sBranchCounts[sPhase.branch] += 1;
      sPrevCarry[sPhase.branch].add(sPhase.phaseAtK2.prev.join(",") + "/" + sPhase.phaseAtK2.carry.join(","));
      sCarryPairs[sPhase.branch].add(sPhase.phaseAtK2.carry.join(","));
      increment(sSectorBranchCounts, sPhase.sector + "/" + sPhase.branch);
      increment(sRHistogram, String(sPhase.r));

      if (sPhase.branch !== sPhase.branchByThreshold) branchMismatches += 1;
      const c = sPhase.phaseAtK2.carry;
      if (sPhase.branch === "L") {
        if (c[0] < -2 || c[0] > 2 || c[1] < -2 || c[1] > 2) carryRectViolations += 1;
      } else {
        if (c[0] < -4 || c[0] > 1 || c[1] < -2 || c[1] > 2) carryRectViolations += 1;
      }
      if (n === 38) index38 = sPhase;
      rootStates += 1;
    }

    const next = highLevelNext(a, d);
    if (n >= 33 && n < 10000 && next !== null) {
      const qNext = phaseAtWindow(next[0], next[1], "q");
      const sNext = phaseAtWindow(next[0], next[1], "S");
      const sourceKey = sKey(sPhase);
      const targetKey = sKey(sNext);
      if (!phaseTransitions.has(sourceKey)) phaseTransitions.set(sourceKey, new Set());
      phaseTransitions.get(sourceKey).add(targetKey);

      const dk = sNext.k - sPhase.k;
      const dj = sNext.j - sPhase.j;
      increment(sShiftHistogram, dk + "," + dj);
      increment(sRTransitionHistogram, sPhase.r + "->" + sNext.r);
      transitions += 1;

      const outX = sPhase.branch === "L"
        ? BigInt(sPhase.x) - 3n * BigInt(sPhase.y) + BigInt(sPhase.C)
        : -4n * BigInt(sPhase.x) - 3n * BigInt(sPhase.y) + BigInt(sPhase.C);
      const outY = sPhase.branch === "L"
        ? 3n * BigInt(sPhase.y) + BigInt(sPhase.F)
        : 3n * BigInt(sPhase.x) + 3n * BigInt(sPhase.y) + BigInt(sPhase.F);
      const nextData = sectorData(next[0], next[1]);
      if (outX !== nextData.x || outY !== nextData.y) affineUpdateMismatches += 1;
    }

    if (n === 10000) break;
    if (next === null) break;
    [a, d] = next;
  }

  const existingQ = new Set(prior.phases.map(p =>
    [p.sector, p.branch, p.prev.join(","), p.carry.join(",")].join("|")
  ));
  const qExactMatch = existingQ.size === qPhases.size &&
    [...existingQ].every(k => qPhases.has(k));

  const outdegreeHistogram = {};
  for (const targets of phaseTransitions.values()) increment(outdegreeHistogram, String(targets.size));

  const qUniqueByBranch = { L: 0, R: 0 };
  for (const k of qPhases) qUniqueByBranch[k.split("|")[1]] += 1;
  const sUniqueByBranch = { L: 0, R: 0 };
  for (const p of sPhases.values()) sUniqueByBranch[p.phase.branch] += 1;

  const output = {
    title: "Machine #623 S-indexed actual boundary phases",
    evidence_type: "finite recurrence diagnostic; not an invariant proof",
    root_indices: [33, 10000],
    root_states: rootStates,
    transitions_between_listed_states: transitions,
    window: {
      convention: "S-indexed",
      buffer: "B=34*ellS+122",
      ellS: "least ell with (3^ell-1)/2 >= S+3",
      word_interval: "[kS+2, jS-2)",
      boundary_phase: "input transducer state entering digit kS+2, after consuming input digit kS+1",
      kS: "least k with 3^k > B",
      jS: "least j with 3^j > B^3",
      r: "jS-3*kS",
    },
    q_window_validation: {
      exact_phase_set_match: qExactMatch,
      existing_unique_phases: existingQ.size,
      recomputed_unique_phases: qPhases.size,
      unique_by_branch: qUniqueByBranch,
      unique_prev_carry: { L: qPrevCarry.L.size, R: qPrevCarry.R.size },
    },
    s_window_summary: {
      unique_complete_phases_including_r: sPhases.size,
      unique_by_branch: sUniqueByBranch,
      unique_prev_carry: { L: sPrevCarry.L.size, R: sPrevCarry.R.size },
      actual_carry_pairs: {
        L: [...sCarryPairs.L].sort(),
        R: [...sCarryPairs.R].sort(),
      },
      sector_branch_counts: sSectorBranchCounts,
      r_histogram: sRHistogram,
      shift_histogram: sShiftHistogram,
      r_transition_histogram: sRTransitionHistogram,
      phase_outdegree_histogram: outdegreeHistogram,
      phase_outdegree_max: Math.max(...[...phaseTransitions.values()].map(s => s.size)),
      branch_selection_mismatches: branchMismatches,
      carry_rectangle_violations: carryRectViolations,
      affine_update_mismatches: affineUpdateMismatches,
      index38_sample: index38,
    },
    universal_carry_rectangles: {
      L: { a: [-2, 2], b: [-2, 2] },
      R: { a: [-4, 1], b: [-2, 2] },
    },
    phases: [...sPhases.values()].sort((x, y) => x.key.localeCompare(y.key)),
    interpretation: "The phase tuple alone is not a closed transition state: its observed transition outdegree reaches 21. The finite product must additionally retain the reset-DFA state and the weighted drain/transducer information; the observed carry pairs are diagnostic only and do not replace the universal rectangles.",
  };

  if (!qExactMatch) throw new Error("q-window validation did not match ActualBoundaryPhases.json");
  if (branchMismatches !== 0 || carryRectViolations !== 0 || affineUpdateMismatches !== 0) {
    throw new Error("branch, carry, or affine validation failed");
  }

  const outputPath = path.join(root, "im-results/agent48-623-tight-window/SWindowBoundaryPhases.json");
  fs.writeFileSync(outputPath, JSON.stringify(output, null, 2) + "\n");
  console.log(JSON.stringify({
    outputPath,
    rootStates,
    transitions,
    qWindowValidation: output.q_window_validation,
    sWindowSummary: output.s_window_summary,
  }, null, 2));
}

collect();
