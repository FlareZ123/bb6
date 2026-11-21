"use strict";

const fs = require("node:fs");
const path = require("node:path");

const product = JSON.parse(fs.readFileSync(
  path.join(__dirname, "ShiftedResetCarryDFA2.json"),
  "utf8"
));

function phaseDelta(sourceR, targetR) {
  if (
    (sourceR === -2 && targetR === -2) ||
    (sourceR === -1 && targetR === -1) ||
    (sourceR === 0 && targetR === 0)
  ) {
    return { deltaK: 0, deltaJ: 0 };
  }
  if (
    (sourceR === -2 && targetR === -1) ||
    (sourceR === -1 && targetR === 0)
  ) {
    return { deltaK: 0, deltaJ: 1 };
  }
  if (sourceR === 0 && targetR === -2) {
    return { deltaK: 1, deltaJ: 1 };
  }
  throw new Error(
    "inadmissible S-window phase edge: " + sourceR + " -> " + targetR
  );
}

/**
 * Compute the exact reset output for the next-next target window.
 *
 * stream is S_n, the source-to-target digit-pair output on
 * [k_n+1, j_{n+1}-2), i.e. through j_{n+1}-3.
 * highExtension is null when deltaJ_{n+1}=0, otherwise the one output
 * digit pair at j_{n+1}-2.
 *
 * The next-next target window is the suffix of stream after
 * 1 + deltaK_n + deltaK_{n+1} symbols, followed by highExtension.
 */
function classifyNextTargetWindow(
  r0,
  r1,
  r2,
  stream,
  highExtension
) {
  const first = phaseDelta(r0, r1);
  const second = phaseDelta(r1, r2);
  const offset = 1 + first.deltaK + second.deltaK;

  if (offset !== 1 && offset !== 2) {
    throw new Error("boundary clock selected an unsupported suffix offset");
  }
  if (first.deltaK === 1 && second.deltaK === 1) {
    throw new Error("phase clock unexpectedly selected suffix offset 3");
  }
  if (!Array.isArray(stream)) {
    throw new Error("stream must be an array of digit pairs");
  }
  if (second.deltaJ === 0 && highExtension !== null) {
    throw new Error("unexpected high extension on a zero-j-shift edge");
  }
  if (second.deltaJ === 1 && highExtension === null) {
    throw new Error("missing high extension on a one-j-shift edge");
  }

  const input = highExtension === null
    ? stream
    : stream.concat([highExtension]);
  let state = product.initial_state;
  const events = [null, null];

  for (const pair of input) {
    if (
      !Array.isArray(pair) ||
      pair.length !== 2 ||
      !Number.isInteger(pair[0]) ||
      !Number.isInteger(pair[1]) ||
      pair[0] < 0 || pair[0] > 2 ||
      pair[1] < 0 || pair[1] > 2
    ) {
      throw new Error("every stream symbol must lie in {0,1,2} x {0,1,2}");
    }

    const symbol = 3 * pair[0] + pair[1];
    const mask = product.event_masks[state][symbol];
    for (let copy = 0; copy < 2; copy += 1) {
      if (mask & (1 << copy)) {
        if (events[copy] !== null) {
          throw new Error("a suffix copy emitted more than one first-reset event");
        }
        events[copy] = symbol;
      }
    }
    state = product.transitions[state][symbol];
  }

  const selected = offset - 1;
  const baseLabelId = product.outputs[state][selected];
  const eventSymbol = events[selected];
  if (baseLabelId === null) {
    if (eventSymbol !== null) {
      throw new Error("event symbol exists without a terminal carry label");
    }
    return {
      reset: false,
      offset,
      deltaK: first.deltaK + second.deltaK,
      deltaJ: second.deltaJ,
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

  const fullLabelId = product.full_output_lookup[eventSymbol][baseLabelId];
  if (fullLabelId === null || fullLabelId === undefined) {
    throw new Error("event/carry pair does not decode to a full output label");
  }

  return {
    reset: true,
    offset,
    deltaK: first.deltaK + second.deltaK,
    deltaJ: second.deltaJ,
    eventSymbol,
    previousPair: [Math.floor(eventSymbol / 3), eventSymbol % 3],
    baseLabelId,
    fullLabelId,
    fullLabel: product.full_output_labels[fullLabelId],
  };
}

module.exports = {
  phaseDelta,
  classifyNextTargetWindow,
};
