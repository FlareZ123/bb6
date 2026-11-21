const fs = require("node:fs");
const path = require("node:path");

const here = __dirname;
const closurePath = path.join(here, "../agent49-parity623/PostResetCarryPairClosure.json");
const resetDfaPath = path.join(here, "../agent49-parity623/ResetPostStateDFA.json");
const sourceProductPath = path.join(here, "../agent24-machine623-shifted-reset-product/SourceCarryResetProduct.json");
const outputPath = path.join(here, "PostResetCarryPairTransducer.json");

const closure = JSON.parse(fs.readFileSync(closurePath, "utf8"));
const resetDfa = JSON.parse(fs.readFileSync(resetDfaPath, "utf8")).post_reset_pair;
const sourceProduct = JSON.parse(fs.readFileSync(sourceProductPath, "utf8"));

const mod3 = n => ((n % 3) + 3) % 3;
const floorDiv3 = n => Math.floor(n / 3);
const tupleKey = xs => xs.join(",");

const leftStateIds = new Map(
  sourceProduct.products.L.transducer_states.map((s, i) => [tupleKey(s), i])
);
const rightStateIds = new Map(
  sourceProduct.products.R.transducer_states.map((s, i) => [tupleKey(s), i])
);

const mismatches = [];
const states = closure.states.map(s => {
  const [px, py] = s.previous_pair;
  const [la, lb] = s.L_carry;
  const [ra, rb] = s.R_carry;
  const L_full_state_id = leftStateIds.get(tupleKey([px, py, la, lb]));
  const R_full_state_id = rightStateIds.get(tupleKey([px, py, ra, rb]));
  if (L_full_state_id === undefined || R_full_state_id === undefined) {
    mismatches.push({ kind: "state", id: s.id, L_full_state_id, R_full_state_id });
  }
  return { ...s, L_full_state_id, R_full_state_id };
});

const transitions = [];
for (const s of states) {
  const [px, py] = s.previous_pair;
  const [la, lb] = s.L_carry;
  const [ra, rb] = s.R_carry;
  for (let x = 0; x < 3; x++) {
    for (let y = 0; y < 3; y++) {
      const txL = x - py + la;
      const tyL = py + lb;
      const txR = -x - px - py + ra;
      const tyR = px + py + rb;
      const L_output = [mod3(txL), mod3(tyL)];
      const R_output = [mod3(txR), mod3(tyR)];
      const next_state_id = closure.transitions[s.id][3 * x + y];
      const next = states[next_state_id];
      const expectedL = [floorDiv3(txL), floorDiv3(tyL)];
      const expectedR = [floorDiv3(txR), floorDiv3(tyR)];
      if (
        next.previous_pair[0] !== x ||
        next.previous_pair[1] !== y ||
        next.L_carry[0] !== expectedL[0] ||
        next.L_carry[1] !== expectedL[1] ||
        next.R_carry[0] !== expectedR[0] ||
        next.R_carry[1] !== expectedR[1]
      ) {
        mismatches.push({
          kind: "transition",
          state_id: s.id,
          input: [x, y],
          next_state_id,
          expectedL,
          expectedR,
          actual: { pair: next.previous_pair, L: next.L_carry, R: next.R_carry }
        });
      }
      if ([...L_output, ...R_output].some(d => d < 0 || d > 2)) {
        mismatches.push({ kind: "output", state_id: s.id, input: [x, y], L_output, R_output });
      }
      transitions.push({
        state_id: s.id,
        input: [x, y],
        input_symbol: 3 * x + y,
        next_state_id,
        L_output,
        R_output
      });
    }
  }
}

const reset_label_map = [];
for (let label_id = 0; label_id < sourceProduct.full_dfa_output_labels.length; label_id++) {
  const label = sourceProduct.full_dfa_output_labels[label_id];
  const L = sourceProduct.products.L.transducer_states[label.L_final_state];
  const R = sourceProduct.products.R.transducer_states[label.R_final_state];
  const seed = states.find(s => s.seed_label_indices.includes(label_id));
  if (
    !seed ||
    tupleKey(L) !== tupleKey([...seed.previous_pair, ...seed.L_carry]) ||
    tupleKey(R) !== tupleKey([...seed.previous_pair, ...seed.R_carry])
  ) {
    mismatches.push({ kind: "reset-label", label_id, L, R, seed_state_id: seed?.id });
  }
  reset_label_map.push({ label_id, seed_state_id: seed?.id });
}

if (mismatches.length !== 0) {
  throw new Error("Paired carry transducer validation failed: " + JSON.stringify(mismatches.slice(0, 10)));
}

const result = {
  schema: "bb6.post-reset-paired-carry-transducer.v1",
  description: "66-state paired L/R carry transducer after a reset label; input symbols are raw source digit pairs, outputs are both branch successor digit pairs.",
  alphabet: { encoding: "3*x+y", x_values: [0, 1, 2], y_values: [0, 1, 2] },
  source_files: [
    "../agent49-parity623/PostResetCarryPairClosure.json",
    "../agent49-parity623/ResetPostStateDFA.json",
    "../agent24-machine623-shifted-reset-product/SourceCarryResetProduct.json"
  ],
  states,
  transitions,
  reset_label_map,
  validation: {
    states_checked: states.length,
    transitions_checked: transitions.length,
    reset_labels_checked: reset_label_map.length,
    mismatches: mismatches.length,
    all_l_y_carries_zero: states.every(s => s.L_carry[1] === 0)
  }
};

fs.writeFileSync(outputPath, JSON.stringify(result, null, 2) + "\n");
console.log(JSON.stringify(result.validation));
