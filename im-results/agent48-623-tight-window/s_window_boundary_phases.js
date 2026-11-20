#!/usr/bin/env node
// Compute actual S-indexed boundary phases for the NEXT-STATE reset word.
// For each source transition D(a,d)->D(a',d'), the tested word is the target
// state D(a',d') on [k'+2,j'-2). The transducer starts with the source-state
// carry at k+1, then consumes input digits k+1,...,k'+1 to reach the phase
// entering the target word at k'+2. Since k'-k is 0 or 1, one or two low
// input digits are consumed.
//
// The q-window calculation is independently compared with the existing
// ActualBoundaryPhases.json to validate the source carry convention.

const fs = require("node:fs");
const path = require("node:path");
const root = process.cwd();
const dfa = JSON.parse(fs.readFileSync(
  path.join(root, "im-results/agent32-623-phase-automaton/ResetPatternDFA.json"), "utf8"
));
const priorQ = JSON.parse(fs.readFileSync(
  path.join(root, "im-results/agent32-623-phase-automaton/ActualBoundaryPhases.json"), "utf8"
));
const postReset = JSON.parse(fs.readFileSync(
  path.join(root, "im-results/agent49-parity623/ResetPostStateDFA.json"), "utf8"
));
const postResetPair = postReset.post_reset_pair;
const postResetPairLength = postReset.post_reset_pair_and_length;
const transitions = dfa.transitions;
const accepting = new Set(dfa.accepting_states);
const initialState = dfa.initial_state;

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

function digitAt(x, i) {
  return Number(mod(floorDiv(x, pow3(i)), 3n));
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
  "LO/L": [-122n, 84n], "LE/L": [-68n, 48n],
  "RO/L": [0n, 0n], "RE/L": [-36n, 18n],
  "LO/R": [-6n, 24n], "LE/R": [-12n, 18n],
  "RO/R": [-44n, 30n], "RE/R": [-20n, 18n],
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

function qWindowPhase(source, stats, C, F, branch) {
  const ell = ellOf(source.q);
  const B = Math.max(34 * ell + 122, 36 * ell + 88);
  const { k } = windowIndices(B);
  const carry = sourceCarry(source, branch, C, F, k);
  const prev = [digitAt(source.x, k), digitAt(source.y, k)];
  return {
    sector: source.sector,
    branch,
    prev,
    carry: [Number(carry[0]), Number(carry[1])],
  };
}

function phaseForTransition(source, target) {
  const sourceEll = ellOf(source.S);
  const targetEll = ellOf(target.S);
  const sourceB = 34 * sourceEll + 122;
  const targetB = 34 * targetEll + 122;
  const sourceWindow = windowIndices(sourceB);
  const targetWindow = windowIndices(targetB);
  const branch = source.g > 0n ? "L" : "R";
  const drainInput = source.q + ({ LO: 3n, LE: 2n, RO: -1n, RE: 1n }[source.sector]);
  const stats = drainStats(drainInput);
  const { C, F } = corrections(source.sector, branch, stats);
  const T = 3n * BigInt(stats.D) + 2n * BigInt(stats.R) +
    ({ LO: 19n, LE: 10n, RO: -4n, RE: 2n }[source.sector]);
  const branchByThreshold = source.g >= T ? "L" : "R";

  let carry = sourceCarry(source, branch, C, F, sourceWindow.k);
  let prev = [digitAt(source.x, sourceWindow.k), digitAt(source.y, sourceWindow.k)];
  const lowOutputs = [];

  // Move the transducer boundary to the NEXT state's k'+2.
  // The source window starts at k+2, while the target starts at k'+2.
  for (let i = sourceWindow.k + 1; i <= targetWindow.k + 1; i += 1) {
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
    lowOutputs.push([Number(mod(tx, 3n)), Number(mod(ty, 3n))]);
    carry = [floorDiv(tx, 3n), floorDiv(ty, 3n)];
    prev = [Number(xi), Number(yi)];
  }

  const kShift = targetWindow.k - sourceWindow.k;
  const jShift = targetWindow.j - sourceWindow.j;
  const sourceR = sourceWindow.j - 3 * sourceWindow.k;
  const targetR = targetWindow.j - 3 * targetWindow.k;
  if (![0, 1].includes(kShift) || ![0, 1].includes(jShift) || (kShift === 1 && jShift !== 1)) {
    throw new Error("S-window shift violates the coupled 0/1 bound");
  }
  if (![ -2, -1, 0 ].includes(sourceR) || ![ -2, -1, 0 ].includes(targetR)) {
    throw new Error("S-window boundary phase r is outside {-2,-1,0}");
  }

  return {
    key: [
      source.sector, branch, target.sector, target.g > 0n ? "L" : "R",
      prev.join(","), Number(carry[0]) + "," + Number(carry[1]),
      sourceR, targetR, kShift, jShift,
    ].join("|"),
    phase: {
      sourceSector: source.sector,
      sourceBranch: branch,
      targetSector: target.sector,
      targetBranch: target.g > 0n ? "L" : "R",
      prev,
      carry: [Number(carry[0]), Number(carry[1])],
      sourceR,
      targetR,
      kShift,
      jShift,
      sourceK: sourceWindow.k,
      targetK: targetWindow.k,
      targetJ: targetWindow.j,
      sourceEll,
      targetEll,
      drainInput: drainInput.toString(),
      drainLength: stats.L,
      n1: stats.n1,
      n2: stats.n2,
      D: stats.D,
      R: stats.R,
      C: C.toString(),
      F: F.toString(),
      T: T.toString(),
      g: source.g.toString(),
      branchByThreshold,
      lowOutputs,
    },
    branch,
    C,
    F,
    stats,
    sourceWindow,
    targetWindow,
  };
}

function firstResetEnd(state, target, branch, C, F, sourceWindow, targetWindow) {
  const xDigits = [];
  const yDigits = [];
  let dfaState = initialState;
  let first = null;
  for (let i = targetWindow.k + 2; i < targetWindow.j - 2; i += 1) {
    const xd = digitAt(target.x, i);
    const yd = digitAt(target.y, i);
    xDigits.push(xd);
    yDigits.push(yd);
    dfaState = transitions[dfaState][xd * 3 + yd];
    if (first === null && accepting.has(dfaState)) first = xDigits.length;
  }
  return { first, length: xDigits.length };
}

function postResetOutput(machine, target, targetWindow) {
  let state = machine.initial_state;
  for (let i = targetWindow.k + 2; i < targetWindow.j - 2; i += 1) {
    const symbol = digitAt(target.x, i) * 3 + digitAt(target.y, i);
    state = machine.transitions[state][symbol];
  }
  const output = machine.outputs[state];
  return output === null ? null : machine.output_labels[output];
}

function addEdge(graph, from, to) {
  if (!graph.has(from)) graph.set(from, new Set());
  graph.get(from).add(to);
}

function graphSummary(graph, allNodes) {
  const outdegreeHistogram = {};
  let edgeCount = 0;
  let multiSuccessorNodes = 0;
  let maxOutdegree = 0;
  for (const targets of graph.values()) {
    const degree = targets.size;
    increment(outdegreeHistogram, String(degree));
    edgeCount += degree;
    if (degree > 1) multiSuccessorNodes += 1;
    maxOutdegree = Math.max(maxOutdegree, degree);
  }
  return {
    nodes: allNodes.size,
    nodesWithSuccessors: graph.size,
    edges: edgeCount,
    multiSuccessorNodes,
    maxOutdegree,
    outdegreeHistogram,
  };
}

function verifyTransducer(source, target, branch, C, F, sourceWindow, targetWindow) {
  let carry = sourceCarry(source, branch, C, F, sourceWindow.k);
  let prev = [digitAt(source.x, sourceWindow.k), digitAt(source.y, sourceWindow.k)];

  // Consume low digits through target k'+1.
  for (let i = sourceWindow.k + 1; i <= targetWindow.k + 1; i += 1) {
    const xi = BigInt(digitAt(source.x, i));
    let tx, ty;
    if (branch === "L") {
      tx = xi - BigInt(prev[1]) + carry[0];
      ty = BigInt(prev[1]) + carry[1];
    } else {
      tx = -xi - BigInt(prev[0]) - BigInt(prev[1]) + carry[0];
      ty = BigInt(prev[0]) + BigInt(prev[1]) + carry[1];
    }
    carry = [floorDiv(tx, 3n), floorDiv(ty, 3n)];
    prev = [digitAt(source.x, i), digitAt(source.y, i)];
  }

  let mismatches = 0;
  for (let i = targetWindow.k + 2; i < targetWindow.j - 2; i += 1) {
    const xi = BigInt(digitAt(source.x, i));
    let tx, ty;
    if (branch === "L") {
      tx = xi - BigInt(prev[1]) + carry[0];
      ty = BigInt(prev[1]) + carry[1];
    } else {
      tx = -xi - BigInt(prev[0]) - BigInt(prev[1]) + carry[0];
      ty = BigInt(prev[0]) + BigInt(prev[1]) + carry[1];
    }
    if (Number(mod(tx, 3n)) !== digitAt(target.x, i)) mismatches += 1;
    if (Number(mod(ty, 3n)) !== digitAt(target.y, i)) mismatches += 1;
    carry = [floorDiv(tx, 3n), floorDiv(ty, 3n)];
    prev = [digitAt(source.x, i), digitAt(source.y, i)];
  }
  return mismatches;
}

function increment(map, key) {
  map[key] = (map[key] || 0) + 1;
}

function collect() {
  let a = 0n;
  let d = 7n;
  const qPhases = new Set();
  const phases = new Map();
  const phaseTransitions = new Map();
  const pairProductTransitions = new Map();
  const pairLengthProductTransitions = new Map();
  const phaseNodes = new Set();
  const pairProductNodes = new Set();
  const pairLengthProductNodes = new Set();
  const postResetPairLabels = {};
  const postResetWitnessLengths = {};
  let previousPhaseKey = null;
  let previousPairProductKey = null;
  let previousPairLengthProductKey = null;
  let postResetPairFailures = 0;
  let postResetPairLengthFailures = 0;
  const sectorBranchCounts = {};
  const rHistogram = {};
  const shiftHistogram = {};
  const rTransitionHistogram = {};
  const firstAcceptHistogram = {};
  const carryPairs = { L: new Set(), R: new Set() };
  const prevCarry = { L: new Set(), R: new Set() };
  let branchMismatches = 0;
  let carryRectangleViolations = 0;
  let affineUpdateMismatches = 0;
  let transducerDigitMismatches = 0;
  let acceptFailures = 0;
  let maxFirstAcceptEnd = 0;
  let transitionsChecked = 0;
  let index38Sample = null;

  for (let n = 0; n <= 10000; n += 1) {
    const next = highLevelNext(a, d);
    if (n >= 33 && next !== null) {
      const source = sectorData(a, d);
      const target = sectorData(next[0], next[1]);
      const sourceEllQ = ellOf(source.q);
      const sourceBQ = Math.max(34 * sourceEllQ + 122, 36 * sourceEllQ + 88);
      const sourceQK = windowIndices(sourceBQ).k;
      const sourceBranch = source.g > 0n ? "L" : "R";
      const drainInput = source.q + ({ LO: 3n, LE: 2n, RO: -1n, RE: 1n }[source.sector]);
      const stats = drainStats(drainInput);
      const { C, F } = corrections(source.sector, sourceBranch, stats);
      const qPhase = qWindowPhase(source, stats, C, F, sourceBranch);
      qPhases.add([qPhase.sector, qPhase.branch, qPhase.prev.join(","), qPhase.carry.join(",")].join("|"));

      const result = phaseForTransition(source, target);
      const p = result.phase;
      const key = result.key;
      phaseNodes.add(key);
      if (previousPhaseKey !== null) addEdge(phaseTransitions, previousPhaseKey, key);
      previousPhaseKey = key;
      if (!phases.has(key)) phases.set(key, { key, count: 0, firstIndex: n, phase: p });
      phases.get(key).count += 1;

      increment(sectorBranchCounts, p.sourceSector + "/" + p.sourceBranch);
      increment(rHistogram, String(p.targetR));
      increment(shiftHistogram, p.kShift + "," + p.jShift);
      increment(rTransitionHistogram, p.sourceR + "->" + p.targetR);
      prevCarry[p.sourceBranch].add(p.prev.join(",") + "/" + p.carry.join(","));
      carryPairs[p.sourceBranch].add(p.carry.join(","));

      if (p.branchByThreshold !== p.sourceBranch) branchMismatches += 1;
      const [ca, cb] = p.carry;
      if (p.sourceBranch === "L") {
        if (ca < -2 || ca > 2 || cb < -2 || cb > 2) carryRectangleViolations += 1;
      } else {
        if (ca < -4 || ca > 1 || cb < -2 || cb > 2) carryRectangleViolations += 1;
      }

      const outX = p.sourceBranch === "L"
        ? source.x - 3n * source.y + result.C
        : -4n * source.x - 3n * source.y + result.C;
      const outY = p.sourceBranch === "L"
        ? 3n * source.y + result.F
        : 3n * source.x + 3n * source.y + result.F;
      if (outX !== target.x || outY !== target.y) affineUpdateMismatches += 1;

      transducerDigitMismatches += verifyTransducer(
        source, target, p.sourceBranch, result.C, result.F,
        result.sourceWindow, result.targetWindow
      );

      const reset = firstResetEnd(
        source, target, p.sourceBranch, result.C, result.F,
        result.sourceWindow, result.targetWindow
      );
      if (reset.first === null) acceptFailures += 1;
      else {
        increment(firstAcceptHistogram, String(reset.first));
        maxFirstAcceptEnd = Math.max(maxFirstAcceptEnd, reset.first);
      }

      const pairLabel = postResetOutput(postResetPair, target, result.targetWindow);
      const pairLengthLabel = postResetOutput(postResetPairLength, target, result.targetWindow);
      if (pairLabel === null) {
        postResetPairFailures += 1;
      } else {
        increment(postResetPairLabels, pairLabel.key);
        const productKey = key + "||" + pairLabel.key;
        pairProductNodes.add(productKey);
        if (previousPairProductKey !== null) addEdge(pairProductTransitions, previousPairProductKey, productKey);
        previousPairProductKey = productKey;
      }
      if (pairLengthLabel === null) {
        postResetPairLengthFailures += 1;
      } else {
        increment(postResetWitnessLengths, String(pairLengthLabel.witness_length));
        const productKey = key + "||" + pairLengthLabel.key;
        pairLengthProductNodes.add(productKey);
        if (previousPairLengthProductKey !== null) addEdge(pairLengthProductTransitions, previousPairLengthProductKey, productKey);
        previousPairLengthProductKey = productKey;
      }

      if (n === 38) index38Sample = p;
      transitionsChecked += 1;
    }

    if (n === 10000) break;
    if (next === null) break;
    [a, d] = next;
  }

  const existingQ = new Set(priorQ.phases.map(p =>
    [p.sector, p.branch, p.prev.join(","), p.carry.join(",")].join("|")
  ));
  const qExactMatch = existingQ.size === qPhases.size &&
    [...existingQ].every(k => qPhases.has(k));

  const phaseGraph = graphSummary(phaseTransitions, phaseNodes);
  const pairProductGraph = graphSummary(pairProductTransitions, pairProductNodes);
  const pairLengthProductGraph = graphSummary(pairLengthProductTransitions, pairLengthProductNodes);

  const byBranch = { L: 0, R: 0 };
  for (const entry of phases.values()) byBranch[entry.phase.sourceBranch] += 1;

  const output = {
    title: "Machine #623 next-state S-window boundary phases",
    evidence_type: "finite recurrence diagnostic; not an invariant proof",
    source_transition_indices: [33, 10000],
    tested_output_states: "D34 through D10001",
    transitions_checked: transitionsChecked,
    window: {
      convention: "S-indexed",
      buffer: "B=34*ellS+122",
      ellS: "least ell with (3^ell-1)/2 >= S+3, S=a+d",
      tested_target_word: "[kS'+2,jS'-2)",
      source_to_target_shift: "kS'-kS,jS'-jS in {(0,0),(0,1),(1,1)}",
      boundary_phase: "source transducer state entering target digit kS'+2 after consuming source input digits kS+1,...,kS'+1",
      r: "jS-3*kS, with source and target r retained",
    },
    q_window_validation: {
      exact_phase_set_match: qExactMatch,
      existing_unique_phases: existingQ.size,
      recomputed_unique_phases: qPhases.size,
    },
    result: {
      accepted: transitionsChecked - acceptFailures,
      failures: acceptFailures,
      max_first_accepting_end: maxFirstAcceptEnd,
      first_accepting_end_histogram: firstAcceptHistogram,
      branch_selection_mismatches: branchMismatches,
      carry_rectangle_violations: carryRectangleViolations,
      affine_update_mismatches: affineUpdateMismatches,
      transducer_digit_mismatches: transducerDigitMismatches,
    },
    phase_transition_graph: phaseGraph,
    post_reset_output: {
      construction: postReset.construction,
      pair: {
        dfa_states: postResetPair.transitions.length,
        labels: postResetPair.output_labels.length,
        observed_labels: Object.keys(postResetPairLabels).length,
        label_histogram: postResetPairLabels,
        failures: postResetPairFailures,
        product_graph: pairProductGraph,
      },
      pair_and_length: {
        dfa_states: postResetPairLength.transitions.length,
        labels: postResetPairLength.output_labels.length,
        observed_witness_lengths: Object.keys(postResetWitnessLengths).length,
        witness_length_histogram: postResetWitnessLengths,
        failures: postResetPairLengthFailures,
        product_graph: pairLengthProductGraph,
      },
    },
    phase_summary: {
      unique_transition_phases: phases.size,
      unique_by_source_branch: byBranch,
      unique_prev_carry: { L: prevCarry.L.size, R: prevCarry.R.size },
      actual_carry_pairs: {
        L: [...carryPairs.L].sort(),
        R: [...carryPairs.R].sort(),
      },
      source_sector_branch_counts: sectorBranchCounts,
      target_r_histogram: rHistogram,
      shift_histogram: shiftHistogram,
      r_transition_histogram: rTransitionHistogram,
      index38_sample: index38Sample,
    },
    universal_carry_rectangles: {
      L: { a: [-2, 2], b: [-2, 2] },
      R: { a: [-4, 1], b: [-2, 2] },
    },
    phases: [...phases.values()].sort((x, y) => x.key.localeCompare(y.key)),
    interpretation: "The phase and post-reset product graphs are finite-prefix evidence only, not all-time transition relations. The post-reset output DFA supplies a compact common L/R transducer-state interface; a proof still needs a closed product with a finite weighted drain/root-language interface. Never replace the universal carry rectangles by observed subsets.",
  };

  if (!qExactMatch) throw new Error("q-window validation did not match ActualBoundaryPhases.json");
  if (branchMismatches || carryRectangleViolations || affineUpdateMismatches || transducerDigitMismatches ||
      acceptFailures || postResetPairFailures || postResetPairLengthFailures) {
    throw new Error("one or more source/scan checks failed");
  }

  const outputPath = path.join(root, "im-results/agent48-623-tight-window/SWindowBoundaryPhases.json");
  fs.writeFileSync(outputPath, JSON.stringify(output, null, 2) + "\n");
  console.log(JSON.stringify({
    outputPath,
    transitionsChecked,
    qWindowValidation: output.q_window_validation,
    result: output.result,
    phaseSummary: output.phase_summary,
    phaseTransitionGraph: output.phase_transition_graph,
    postResetOutput: output.post_reset_output,
  }, null, 2));
}

collect();
