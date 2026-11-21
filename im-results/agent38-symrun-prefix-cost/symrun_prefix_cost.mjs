#!/usr/bin/env node
/*
 * Exact primitive-cost replay of the initial runElemFast phase for upstream
 * Cryptids F424 and F412.
 *
 * Source pin:
 *   google-deepmind/cryptids
 *   3647718b5df22e1a61462dec0376bd204526285a
 *   BusyBeaver/Calculi/HaltShared.lean
 *
 * This is a transparent JavaScript translation of stepElemM and the
 * machine-specific HasSymRunRules proof costs. It is computational evidence,
 * not a Lean theorem and not the complete halting time.
 *
 * MItem encoding: -1 = .zero; n >= 0 = .run n.
 */

function bumpM(xs) {
  if (xs.length === 0) return [0];
  return [xs[0] === -1 ? 0 : xs[0] + 1, ...xs.slice(1)];
}

function zeros(n) {
  return Array(n).fill(-1);
}

function stepElemM(state, costs, stats) {
  const [mode, L, R] = state;
  let next;
  let cost;
  let rule;
  let parameter = null;

  if (mode === "BB") {
    if (L.length === 0) {
      next = ["CB", [], bumpM(R)];
      cost = 1;
      rule = "step_BB_nil";
    } else if (L[0] === -1) {
      next = ["CB", L.slice(1), bumpM(R)];
      cost = 1;
      rule = "step_BB_zero";
    } else if (L[0] === 0) {
      next = ["BB", L.slice(1), [0, ...R]];
      cost = costs.bbRun0;
      rule = "step_BB_run0";
    } else if (L[0] === 1) {
      next = ["BB", L.slice(1), [0, ...bumpM(R)]];
      cost = 3;
      rule = "step_BB_run1";
    } else if (L[0] === 2) {
      next = ["DL", L.slice(1), [0, 0, ...bumpM(R)]];
      cost = 5;
      rule = "step_BB_run2";
    } else if (L[0] === 3) {
      next = ["BB", [0, -1, -1, ...L.slice(1)], bumpM(R)];
      cost = 9;
      rule = "step_BB_run3";
    } else {
      next = ["BB", [0, -1, L[0] - 4, ...L.slice(1)], bumpM(R)];
      cost = 9;
      rule = "step_BB_run_ge4";
    }
  } else if (mode === "DL") {
    if (L.length === 0) {
      next = state;
      cost = 0;
      rule = "step_DL_stutter";
    } else if (L[0] === -1) {
      next = ["HALT", L, R];
      cost = 0;
      rule = "step_DL_zero";
    } else if (L[0] === 0) {
      next = ["BB", L.slice(1), bumpM(R)];
      cost = 1;
      rule = "step_DL_run0";
    } else if (L[0] === 1) {
      next = ["DL", L.slice(1), [0, ...bumpM(R)]];
      cost = 3;
      rule = "step_DL_run1";
    } else if (L[0] === 2 && R.length > 0 && R[0] >= 0) {
      const d0 = R[0];
      next = ["CB", [0, 0, ...zeros(d0 + 1), ...L.slice(1)], R.slice(1)];
      cost = 6 + 3 * (d0 + 1) + costs.exitRA;
      rule = "step_DL_run2";
      parameter = d0;
    } else {
      next = state;
      cost = 0;
      rule = "step_DL_stutter";
    }
  } else if (mode === "CB") {
    if (R.length === 0) {
      next = ["DL", bumpM(L), [0]];
      cost = 2;
      rule = "step_CB_nil";
    } else if (R[0] === -1) {
      next = ["DL", bumpM(L), bumpM(R.slice(1))];
      cost = 2;
      rule = "step_CB_zero";
    } else if (R[0] === 0) {
      if (R.length === 1) {
        next = ["BB", [0, ...bumpM(L)], []];
        cost = 3;
        rule = "step_CB_run0_nil";
      } else if (R[1] === -1) {
        next = ["BB", [0, ...bumpM(L)], R.slice(2)];
        cost = 3;
        rule = "step_CB_run0_zero";
      } else if (R[1] === 0) {
        next = ["BB", [0, -1, ...bumpM(L)], R.slice(2)];
        cost = 6;
        rule = "step_CB_run0_run0";
      } else {
        const d2 = R[1] - 1;
        next = ["CB", [0, 0, ...zeros(d2), ...bumpM(L)], R.slice(2)];
        cost = 5 + 3 * (d2 + 1) + costs.exitRA;
        rule = "step_CB_run0_run_pos";
        parameter = d2;
      }
    } else if (R[0] === 1) {
      next = ["CB", [0, ...bumpM(L)], R.slice(1)];
      cost = 3;
      rule = "step_CB_run1";
    } else if (R[0] === 2) {
      next = ["BB", bumpM(L), [0, -1, ...R.slice(1)]];
      cost = 5;
      rule = "step_CB_run2";
    } else {
      next = ["BB", bumpM(L), [0, R[0] - 3, ...R.slice(1)]];
      cost = 5;
      rule = "step_CB_run_ge3";
    }
  } else {
    next = state;
    cost = 0;
    rule = "HALT";
  }

  stats.counts[rule] = (stats.counts[rule] || 0) + 1;
  stats.costs[rule] = (stats.costs[rule] || 0) + cost;
  if (parameter !== null) {
    const key = rule === "step_DL_run2" ? "d0" : "d2";
    stats.parameters[key].push(parameter);
  }
  return [next, cost];
}

function runPrefix({name, params, start, bbRun0, exitRA, entryCost, expectedRight}) {
  const [a, b, c, d] = params;
  const iterations = d * 4096 + c * 256 + b * 16 + a;
  let state = start;
  let primitiveCost = 0;
  let maxRun = 0;
  let maxListLength = 0;
  const stats = {counts: {}, costs: {}, parameters: {d0: [], d2: []}};

  for (let i = 0; i < iterations; i++) {
    const [next, cost] = stepElemM(state, {bbRun0, exitRA}, stats);
    state = next;
    primitiveCost += cost;
    for (const x of [...state[1], ...state[2]]) {
      if (x >= 0) maxRun = Math.max(maxRun, x);
    }
    maxListLength = Math.max(maxListLength, state[1].length, state[2].length);
    if (state[0] === "HALT") {
      throw new Error(name + " halted before runElemFast completed at iteration " + (i + 1));
    }
  }

  // Decode the source initSymCyc3 token lists. On the left, repB1 46
  // expands to 46 copies of [.run 0, .run 1], followed by .run 0.
  const expectedLeft = [0, 0, 1, 1, 0, 1, 1, 1, 0, -1, 1];
  for (let i = 0; i < 46; i++) expectedLeft.push(0, 1);
  expectedLeft.push(0);
  const expected = ["CB", expectedLeft, expectedRight];
  const finalStateMatchesInitSymCyc3 =
    JSON.stringify(state) === JSON.stringify(expected);

  const sum = xs => xs.reduce((x, y) => x + y, 0);
  const variableBranches = {
    DL: {
      count: stats.parameters.d0.length,
      sumD0: sum(stats.parameters.d0),
      maxD0: Math.max(0, ...stats.parameters.d0)
    },
    CB: {
      count: stats.parameters.d2.length,
      sumD2: sum(stats.parameters.d2),
      maxD2: Math.max(0, ...stats.parameters.d2)
    }
  };

  if (!finalStateMatchesInitSymCyc3) {
    throw new Error(name + " did not reproduce initSymCyc3");
  }
  if (Object.values(stats.counts).reduce((x, y) => x + y, 0) !== iterations) {
    throw new Error(name + " branch count does not equal iteration count");
  }

  return {
    machine: name,
    runElemFastParameters: params,
    stepElemMIterations: iterations,
    primitiveCostWithinRunElemFast: primitiveCost,
    initialEntryCost: entryCost,
    finalHaltStepCost: 1,
    knownPrefixCostIncludingEntryAndFinal: primitiveCost + entryCost + 1,
    variableBranches,
    maxRunParameterSeen: maxRun,
    maxDecodedListLengthSeen: maxListLength,
    branchCounts: stats.counts,
    branchPrimitiveCosts: stats.costs,
    finalStateMatchesInitSymCyc3
  };
}

const results = [
  runPrefix({
    name: "F424",
    params: [1, 1, 11, 4],
    start: ["CB", [], [1, 0]],
    bbRun0: 8,
    exitRA: 13,
    entryCost: 18,
    expectedRight: [79, 0, 1, -1, 1, 1, 1, 1, 1]
  }),
  runPrefix({
    name: "F412",
    params: [7, 3, 11, 4],
    start: ["BB", [0], []],
    bbRun0: 6,
    exitRA: 11,
    entryCost: 1,
    expectedRight: [79, 0, 1, -1, 1, 1, 1, 1, 1, 1]
  })
];

console.log(JSON.stringify(results, null, 2));
