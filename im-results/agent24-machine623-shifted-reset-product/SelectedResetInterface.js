"use strict";

const fs = require("node:fs");
const path = require("node:path");

const artifact = JSON.parse(fs.readFileSync(
  path.join(__dirname, "OffsetSelectedResetDFA.json"),
  "utf8"
));

function selectOffset(sourceR, targetR) {
  if (
    (sourceR === -2 && targetR === -2) ||
    (sourceR === -1 && targetR === -1) ||
    (sourceR === 0 && targetR === 0) ||
    (sourceR === -2 && targetR === -1) ||
    (sourceR === -1 && targetR === 0)
  ) {
    return 1;
  }
  if (sourceR === 0 && targetR === -2) return 2;
  throw new Error(
    "inadmissible S-window phase edge: " + sourceR + " -> " + targetR
  );
}

/**
 * Classify the exact target S-window using the source-to-target output stream.
 *
 * lowOutputs must contain output digit pairs at k+1,...,k'+1.
 * targetWord must contain target digit pairs at k'+2,...,j'-3 inclusive.
 * Do not append digits above j'-3.
 */
function classifyTargetWindow(sourceR, targetR, lowOutputs, targetWord) {
  const offset = selectOffset(sourceR, targetR);
  if (!Array.isArray(lowOutputs) || lowOutputs.length !== offset) {
    throw new Error(
      "low-output prefix length must equal selected offset " + offset
    );
  }
  if (!Array.isArray(targetWord)) {
    throw new Error("targetWord must be an array of digit pairs");
  }

  let state = artifact.initial_state_by_offset[String(offset)];
  let eventSymbol = null;

  for (const pair of lowOutputs.concat(targetWord)) {
    if (
      !Array.isArray(pair) ||
      pair.length !== 2 ||
      !Number.isInteger(pair[0]) ||
      !Number.isInteger(pair[1]) ||
      pair[0] < 0 || pair[0] > 2 ||
      pair[1] < 0 || pair[1] > 2
    ) {
      throw new Error("every output pair must lie in {0,1,2} x {0,1,2}");
    }

    const symbol = 3 * pair[0] + pair[1];
    if (artifact.event_masks[state][symbol] & 1) {
      if (eventSymbol !== null) {
        throw new Error("selected copy emitted more than one first-reset event");
      }
      eventSymbol = symbol;
    }
    state = artifact.transitions[state][symbol];
  }

  const baseLabelId = artifact.outputs[state];
  if (baseLabelId === null) {
    if (eventSymbol !== null) {
      throw new Error("event symbol exists without a terminal carry label");
    }
    return {
      reset: false,
      offset,
      eventSymbol: null,
      previousPair: null,
      baseLabelId: null,
      fullLabelId: null,
      fullLabel: null,
    };
  }

  if (eventSymbol === null) {
    throw new Error("terminal carry label has no first-reset event symbol");
  }

  const fullLabelId = artifact.full_output_lookup[eventSymbol][baseLabelId];
  if (fullLabelId === null || fullLabelId === undefined) {
    throw new Error("event/carry pair does not decode to a full output label");
  }

  return {
    reset: true,
    offset,
    eventSymbol,
    previousPair: [Math.floor(eventSymbol / 3), eventSymbol % 3],
    baseLabelId,
    fullLabelId,
    fullLabel: artifact.full_output_labels[fullLabelId],
  };
}

module.exports = {
  selectOffset,
  classifyTargetWindow,
};
