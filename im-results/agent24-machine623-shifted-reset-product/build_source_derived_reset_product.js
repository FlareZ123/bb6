#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");

const root = process.cwd();
const oldDfaPath = path.join(root, "im-results/agent32-623-phase-automaton/ResetPatternDFA.json");
const outputPath = path.join(root, "im-results/agent24-machine623-shifted-reset-product/SourceDerivedResetProduct.json");

function mod3(n) {
  return ((n % 3) + 3) % 3;
}
function decodeWord(code, length) {
  const word = Array(length);
  for (let i = length - 1; i >= 0; i--) {
    word[i] = code % 9;
    code = Math.floor(code / 9);
  }
  return word;
}

function buildTransducer(branch) {
  const carryMinX = branch === "L" ? -2 : -4;
  const carryMaxX = branch === "L" ? 2 : 1;
  const carryCountX = carryMaxX - carryMinX + 1;
  const states = [];
  const index = new Map();

  for (let prevX = 0; prevX < 3; prevX++) {
    for (let prevY = 0; prevY < 3; prevY++) {
      for (let carryX = carryMinX; carryX <= carryMaxX; carryX++) {
        for (let carryY = -2; carryY <= 2; carryY++) {
          index.set([prevX, prevY, carryX, carryY].join(","), states.length);
          states.push([prevX, prevY, carryX, carryY]);
        }
      }
    }
  }

  const next = new Int32Array(states.length * 9);
  next.fill(-1);
  const xFlags = new Uint8Array(states.length * 9);

  for (let state = 0; state < states.length; state++) {
    const [prevX, prevY, carryX, carryY] = states[state];
    for (let x = 0; x < 3; x++) {
      for (let y = 0; y < 3; y++) {
        const tx = branch === "L"
          ? x - prevY + carryX
          : -x - prevX - prevY + carryX;
        const ty = branch === "L"
          ? prevY + carryY
          : prevX + prevY + carryY;
        const nextCarryX = Math.floor(tx / 3);
        const nextCarryY = Math.floor(ty / 3);
        if (
          nextCarryX < carryMinX || nextCarryX > carryMaxX ||
          nextCarryY < -2 || nextCarryY > 2
        ) {
          throw new Error(branch + ": full transducer rectangle is not closed");
        }
        const nextState = index.get([x, y, nextCarryX, nextCarryY].join(","));
        const symbol = state * 9 + x * 3 + y;
        next[symbol] = nextState;
        const outX = mod3(tx);
        xFlags[symbol] = (outX !== 0 ? 1 : 0) | (outX !== 2 ? 2 : 0);
      }
    }
  }

  return {
    branch,
    carryMinX,
    carryMaxX,
    carryCountX,
    states,
    index,
    next,
    xFlags
  };
}

function sourceDerivedStarts(transducer) {
  const starts = [];
  for (let prevX = 0; prevX < 3; prevX++) {
    for (let prevY = 0; prevY < 3; prevY++) {
      const minX = transducer.branch === "L" ? -2 : -4;
      const maxX = transducer.branch === "L" ? 1 : 0;
      const minY = -1;
      const maxY = transducer.branch === "L" ? 1 : 2;
      for (let carryX = minX; carryX <= maxX; carryX++) {
        for (let carryY = minY; carryY <= maxY; carryY++) {
          starts.push(transducer.index.get(
            [prevX, prevY, carryX, carryY].join(",")
          ));
        }
      }
    }
  }
  return starts;
}

function enumerateMinimalPatterns(L, R, startsL, startsR) {
  const nL = startsL.length;
  const nR = startsR.length;
  const total = nL + nR;
  const initial = new Uint32Array(total);
  initial.set(startsL);
  initial.set(startsR, nL);
  const stateStack = Array.from({ length: 7 }, () => new Uint32Array(total));
  const flagStack = Array.from({ length: 7 }, () => new Uint8Array(total));
  const patterns = {
    3: new Set(),
    4: new Set(),
    5: new Set(),
    6: new Set()
  };

  function hasShorterPattern(word) {
    for (let length = 3; length < word.length; length++) {
      for (let start = 0; start + length <= word.length; start++) {
        let code = 0;
        for (let i = 0; i < length; i++) code = code * 9 + word[start + i];
        if (patterns[length].has(code)) return true;
      }
    }
    return false;
  }

  function isCommonReset(states, flags) {
    for (let i = 0; i < total; i++) if (flags[i] !== 3) return false;
    for (let i = 1; i < nL; i++) if (states[i] !== states[0]) return false;
    for (let i = nL + 1; i < total; i++) if (states[i] !== states[nL]) return false;
    return true;
  }

  let visitedPrefixes = 0;
  function visit(depth, states, flags, word, code) {
    visitedPrefixes++;
    if (depth >= 3 && hasShorterPattern(word)) return;
    if (depth >= 3 && isCommonReset(states, flags)) {
      patterns[depth].add(code);
      return;
    }
    if (depth === 6) return;

    const nextStates = stateStack[depth + 1];
    const nextFlags = flagStack[depth + 1];
    for (let symbol = 0; symbol < 9; symbol++) {
      let valid = true;
      for (let i = 0; i < total; i++) {
        const transducer = i < nL ? L : R;
        const transition = states[i] * 9 + symbol;
        const next = transducer.next[transition];
        if (next < 0) {
          valid = false;
          break;
        }
        nextStates[i] = next;
        nextFlags[i] = flags[i] | transducer.xFlags[transition];
      }
      if (valid) {
        word.push(symbol);
        visit(depth + 1, nextStates, nextFlags, word, code * 9 + symbol);
        word.pop();
      }
    }
  }

  visit(0, initial, new Uint8Array(total), [], 0);
  return { patterns, visitedPrefixes };
}

function buildResetDfa(patterns) {
  const go = [new Int32Array(9)];
  go[0].fill(-1);
  const fail = [0];
  const terminal = [0];
  let ahoStates = 1;

  for (let length = 3; length <= 6; length++) {
    for (const code of patterns[length]) {
      let state = 0;
      for (const symbol of decodeWord(code, length)) {
        let target = go[state][symbol];
        if (target < 0) {
          target = ahoStates++;
          go[state][symbol] = target;
          const row = new Int32Array(9);
          row.fill(-1);
          go.push(row);
          fail.push(0);
          terminal.push(0);
        }
        state = target;
      }
      terminal[state] = length;
    }
  }

  const ahoOutput = new Uint8Array(ahoStates);
  const queue = [];
  for (let symbol = 0; symbol < 9; symbol++) {
    const target = go[0][symbol];
    if (target >= 0) {
      fail[target] = 0;
      ahoOutput[target] = terminal[target];
      queue.push(target);
    } else {
      go[0][symbol] = 0;
    }
  }

  for (let head = 0; head < queue.length; head++) {
    const state = queue[head];
    for (let symbol = 0; symbol < 9; symbol++) {
      const target = go[state][symbol];
      if (target >= 0) {
        const failure = go[fail[state]][symbol];
        const own = terminal[target];
        const inherited = ahoOutput[failure];
        fail[target] = failure;
        ahoOutput[target] = own && inherited
          ? Math.min(own, inherited)
          : (own || inherited);
        queue.push(target);
      } else {
        go[state][symbol] = go[fail[state]][symbol];
      }
    }
  }

  const sink = ahoStates;
  const rawStateCount = ahoStates + 1;
  const accepting = new Uint8Array(rawStateCount);
  const transitions = Array.from(
    { length: rawStateCount },
    () => new Uint32Array(9)
  );
  accepting[sink] = 1;

  for (let state = 0; state < ahoStates; state++) {
    accepting[state] = ahoOutput[state] ? 1 : 0;
    for (let symbol = 0; symbol < 9; symbol++) {
      const target = go[state][symbol];
      transitions[state][symbol] =
        (accepting[state] || ahoOutput[target]) ? sink : target;
    }
  }
  transitions[sink].fill(sink);

  let classes = Uint32Array.from(accepting);
  const partitionCounts = [];
  let previousCount = -1;
  for (let round = 0; round < 32; round++) {
    const signatureIndex = new Map();
    const nextClasses = new Uint32Array(rawStateCount);
    for (let state = 0; state < rawStateCount; state++) {
      const signature =
        classes[state] + "," +
        Array.from(transitions[state], target => classes[target]).join(",");
      let classId = signatureIndex.get(signature);
      if (classId === undefined) {
        classId = signatureIndex.size;
        signatureIndex.set(signature, classId);
      }
      nextClasses[state] = classId;
    }
    classes = nextClasses;
    partitionCounts.push(signatureIndex.size);
    if (signatureIndex.size === previousCount) break;
    previousCount = signatureIndex.size;
  }

  const stateCount = partitionCounts[partitionCounts.length - 1];
  const representatives = Array(stateCount).fill(-1);
  for (let state = 0; state < rawStateCount; state++) {
    if (representatives[classes[state]] < 0) {
      representatives[classes[state]] = state;
    }
  }

  const minimizedTransitions = representatives.map(state =>
    Array.from(transitions[state], target => classes[target])
  );
  const minimizedAccepting = representatives
    .map((state, classId) => accepting[state] ? classId : -1)
    .filter(classId => classId >= 0);

  return {
    state_count: stateCount,
    initial_state: classes[0],
    accepting_states: minimizedAccepting,
    transitions: minimizedTransitions,
    aho_corasick_state_count: ahoStates,
    minimization_partition_counts: partitionCounts
  };
}

function checkResetWord(transducer, starts, word) {
  let commonFinal = null;
  let common = true;
  let allXNonmonochromatic = true;

  for (const initialState of starts) {
    let state = initialState;
    let flags = 0;
    for (const symbol of word) {
      const transition = state * 9 + symbol;
      flags |= transducer.xFlags[transition];
      state = transducer.next[transition];
    }
    if (commonFinal === null) commonFinal = state;
    else if (state !== commonFinal) common = false;
    if (flags !== 3) allXNonmonochromatic = false;
  }

  return {
    starts: starts.length,
    finalState: transducer.states[commonFinal],
    common,
    allXNonmonochromatic
  };
}

function compareLanguages(oldDfa, newDfa) {
  const oldAccepting = new Set(oldDfa.accepting_states);
  const newAccepting = new Set(newDfa.accepting_states);
  const seen = new Set();
  const queue = [[oldDfa.initial_state, newDfa.initial_state, []]];
  let oldOnly = null;
  let newOnly = null;

  for (let head = 0; head < queue.length; head++) {
    const [oldState, newState, word] = queue[head];
    const key = oldState + "," + newState;
    if (seen.has(key)) continue;
    seen.add(key);

    if (oldAccepting.has(oldState) && !newAccepting.has(newState) && oldOnly === null) {
      oldOnly = word;
    }
    if (newAccepting.has(newState) && !oldAccepting.has(oldState) && newOnly === null) {
      newOnly = word;
    }
    if (oldOnly !== null && newOnly !== null) break;

    for (let symbol = 0; symbol < 9; symbol++) {
      queue.push([
        oldDfa.transitions[oldState][symbol],
        newDfa.transitions[newState][symbol],
        word.length < 10 ? word.concat(symbol) : word
      ]);
    }
  }

  return {
    full_rectangle_dfa_state_count: oldDfa.transitions.length,
    full_language_subset_of_source_derived_language: oldOnly === null,
    shortest_source_only_witness: newOnly,
    product_pairs_visited: seen.size
  };
}

function buildProduct(branch, transducer, sourceStarts, resetDfa) {
  const dfaStateCount = resetDfa.state_count;
  const skip1 = dfaStateCount;
  const skip2 = dfaStateCount + 1;
  const productDfaCount = dfaStateCount + 2;
  const acceptingSet = new Set(resetDfa.accepting_states);

  function nextDfaState(state, symbol) {
    if (state < dfaStateCount) return resetDfa.transitions[state][symbol];
    return state === skip1 ? resetDfa.initial_state : skip1;
  }
  function dfaOutput(state) {
    return state < dfaStateCount && acceptingSet.has(state) ? 1 : 0;
  }

  const productStates = [];
  const productIndex = new Map();
  const productTransitions = [];
  function addState(transducerState, dfaState) {
    const key = transducerState * productDfaCount + dfaState;
    let index = productIndex.get(key);
    if (index === undefined) {
      index = productStates.length;
      productIndex.set(key, index);
      productStates.push([transducerState, dfaState]);
    }
    return index;
  }

  const startsByOffset = { "1": [], "2": [] };
  for (const transducerState of sourceStarts) {
    startsByOffset["1"].push(addState(transducerState, skip1));
    startsByOffset["2"].push(addState(transducerState, skip2));
  }

  for (let i = 0; i < productStates.length; i++) {
    const [transducerState, dfaState] = productStates[i];
    const [prevX, prevY, carryX, carryY] = transducer.states[transducerState];
    productTransitions[i] = Array.from({ length: 9 }, (_, symbol) => {
      const x = Math.floor(symbol / 3);
      const y = symbol % 3;
      const tx = branch === "L"
        ? x - prevY + carryX
        : -x - prevX - prevY + carryX;
      const ty = branch === "L"
        ? prevY + carryY
        : prevX + prevY + carryY;
      const nextTransducerState = transducer.next[transducerState * 9 + symbol];
      const outputSymbol = 3 * mod3(tx) + mod3(ty);
      return addState(
        nextTransducerState,
        nextDfaState(dfaState, outputSymbol)
      );
    });
  }

  const outputs = productStates.map(([, dfaState]) => dfaOutput(dfaState));
  let classes = Uint32Array.from(outputs);
  const partitionCounts = [new Set(classes).size];
  let stable = false;

  for (let round = 0; round < 40; round++) {
    const signatureIndex = new Map();
    const nextClasses = new Uint32Array(productStates.length);
    for (let i = 0; i < productStates.length; i++) {
      const signature =
        outputs[i] + "," +
        productTransitions[i].map(next => classes[next]).join(",");
      let classId = signatureIndex.get(signature);
      if (classId === undefined) {
        classId = signatureIndex.size;
        signatureIndex.set(signature, classId);
      }
      nextClasses[i] = classId;
    }
    partitionCounts.push(signatureIndex.size);

    const oldToNew = new Map();
    const newToOld = new Map();
    stable = true;
    for (let i = 0; i < classes.length; i++) {
      if (oldToNew.has(classes[i]) && oldToNew.get(classes[i]) !== nextClasses[i]) {
        stable = false;
      }
      if (newToOld.has(nextClasses[i]) && newToOld.get(nextClasses[i]) !== classes[i]) {
        stable = false;
      }
      oldToNew.set(classes[i], nextClasses[i]);
      newToOld.set(nextClasses[i], classes[i]);
    }
    classes = nextClasses;
    if (stable) break;
  }
  if (!stable) throw new Error(branch + ": product Moore minimization did not stabilize.");

  const minimizedStateCount = new Set(classes).size;
  const representatives = Array(minimizedStateCount).fill(-1);
  for (let i = 0; i < classes.length; i++) {
    if (representatives[classes[i]] < 0) representatives[classes[i]] = i;
  }
  const quotientOutputs = representatives.map(i => outputs[i]);
  const quotientTransitions = representatives.map(i =>
    productTransitions[i].map(next => classes[next])
  );

  for (let i = 0; i < productStates.length; i++) {
    const classId = classes[i];
    if (outputs[i] !== quotientOutputs[classId]) {
      throw new Error(branch + ": quotient output check failed.");
    }
    for (let symbol = 0; symbol < 9; symbol++) {
      if (classes[productTransitions[i][symbol]] !== quotientTransitions[classId][symbol]) {
        throw new Error(branch + ": quotient transition check failed.");
      }
    }
  }

  const acceptingProductIds = [];
  for (let i = 0; i < outputs.length; i++) if (outputs[i] === 1) acceptingProductIds.push(i);
  const acceptingTransducerIds = [...new Set(
    acceptingProductIds.map(i => productStates[i][0])
  )].sort((a, b) => a - b);
  const acceptingTransducerStates = acceptingTransducerIds.map(i => transducer.states[i]);
  const acceptedRegionClosed = acceptingProductIds.every(i =>
    productTransitions[i].every(next => outputs[next] === 1)
  );
  if (!acceptedRegionClosed) {
    throw new Error(branch + ": accepted product region is not closed.");
  }

  return {
    branch,
    full_transducer_state_count: transducer.states.length,
    source_derived_start_count: sourceStarts.length,
    source_start_transducer_ids: sourceStarts,
    transducer_states: transducer.states,
    product_states: productStates,
    class_of_product_state: Array.from(classes),
    initial_classes_by_offset: {
      "1": startsByOffset["1"].map(i => classes[i]),
      "2": startsByOffset["2"].map(i => classes[i])
    },
    quotient_outputs: Array.from(quotientOutputs),
    quotient_transitions: quotientTransitions,
    partition_counts: partitionCounts,
    product_state_count: productStates.length,
    product_transition_count: productTransitions.length * 9,
    minimized_state_count: minimizedStateCount,
    accepting_product_state_count: acceptingProductIds.length,
    accepting_transducer_states: acceptingTransducerStates,
    accepted_region_closed: acceptedRegionClosed
  };
}

const L = buildTransducer("L");
const R = buildTransducer("R");
const startsL = sourceDerivedStarts(L);
const startsR = sourceDerivedStarts(R);
const enumeration = enumerateMinimalPatterns(L, R, startsL, startsR);
const resetDfa = buildResetDfa(enumeration.patterns);
const oldDfa = JSON.parse(fs.readFileSync(oldDfaPath, "utf8"));
const languageComparison = compareLanguages(oldDfa, resetDfa);
if (!languageComparison.full_language_subset_of_source_derived_language) {
  throw new Error("The full-rectangle reset language is not included in the source-derived language.");
}

const resetWord = [1, 0, 0];
const directL = checkResetWord(L, startsL, resetWord);
const directR = checkResetWord(R, startsR, resetWord);
if (
  !directL.common || !directL.allXNonmonochromatic ||
  !directR.common || !directR.allXNonmonochromatic ||
  JSON.stringify(directL.finalState) !== JSON.stringify([0, 0, -1, 0]) ||
  JSON.stringify(directR.finalState) !== JSON.stringify([0, 0, -1, 0])
) {
  throw new Error("The proposed three-symbol reset word failed direct verification.");
}

const fullLStarts = [];
for (let prevX = 0; prevX < 3; prevX++) {
  for (let prevY = 0; prevY < 3; prevY++) {
    for (let carryX = -2; carryX <= 2; carryX++) {
      for (let carryY = -2; carryY <= 2; carryY++) {
        fullLStarts.push(L.index.get([prevX, prevY, carryX, carryY].join(",")));
      }
    }
  }
}
const excludedLStart = L.index.get([0, 0, 2, -2].join(","));
const excludedLCheck = checkResetWord(L, [excludedLStart], resetWord);
if (excludedLCheck.allXNonmonochromatic) {
  throw new Error("The full-L counterexample no longer falsifies the nonmonochromatic condition.");
}

const artifact = {
  schema: "bb6-machine623-source-derived-reset-product-v1",
  source_carry_bounds_source: "im-results/agent24-machine623-shifted-reset-product/StartCarryRectangleInclusion.md",
  source_carry_bounds: {
    L: { carry_x: [-2, 1], carry_y: [-1, 1], previous_pair_count: 9, start_count: startsL.length },
    R: { carry_x: [-4, 0], carry_y: [-1, 2], previous_pair_count: 9, start_count: startsR.length }
  },
  full_transducer_rectangles: {
    L: { carry_x: [-2, 2], carry_y: [-2, 2], state_count: L.states.length },
    R: { carry_x: [-4, 1], carry_y: [-2, 2], state_count: R.states.length }
  },
  reset_pattern_dfa: {
    state_count: resetDfa.state_count,
    initial_state: resetDfa.initial_state,
    accepting_states: resetDfa.accepting_states,
    transitions: resetDfa.transitions,
    minimal_pattern_counts: Object.fromEntries(
      [3, 4, 5, 6].map(length => [length, enumeration.patterns[length].size])
    ),
    total_minimal_patterns: [3, 4, 5, 6].reduce(
      (sum, length) => sum + enumeration.patterns[length].size, 0
    ),
    aho_corasick_state_count: resetDfa.aho_corasick_state_count,
    minimization_partition_counts: resetDfa.minimization_partition_counts,
    maximum_pattern_length: 6
  },
  language_comparison_with_full_rectangle_dfa: languageComparison,
  direct_three_symbol_reset: {
    word: resetWord,
    notation: "01 00 00",
    L: directL,
    R: directR,
    common_final_state: [0, 0, -1, 0],
    full_L_rectangle_counterexample_start: [0, 0, 2, -2]
  },
  products: {
    L: buildProduct("L", L, startsL, resetDfa),
    R: buildProduct("R", R, startsR, resetDfa)
  }
};

const serialized = JSON.stringify(artifact, null, 2) + "\n";
if (process.argv.includes("--verify")) {
  const existing = JSON.parse(fs.readFileSync(outputPath, "utf8"));
  if (JSON.stringify(existing) !== JSON.stringify(artifact)) {
    throw new Error("Stored SourceDerivedResetProduct.json differs from regenerated artifact.");
  }
  process.stdout.write("Verified SourceDerivedResetProduct.json\n");
} else {
  fs.writeFileSync(outputPath, serialized);
  process.stdout.write("Wrote SourceDerivedResetProduct.json (" + serialized.length + " bytes)\n");
}
