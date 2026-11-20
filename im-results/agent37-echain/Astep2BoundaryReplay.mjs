#!/usr/bin/env node
// Reproducible boundary replay of the pinned external Lean A_step2 chain.
// Run: node Astep2BoundaryReplay.mjs [--trace]
//
// The simulator keeps the current head in right[0].  Thus side2, the
// right-hand tape in the step_01C_C11 lemma, is right.slice(1), not right.

const TM = {
  A: { 0: [1, "R", "B"], 1: [0, "R", "E"] },
  B: { 0: [1, "L", "C"], 1: [0, "R", "A"] },
  C: { 0: [1, "L", "A"], 1: [1, "L", "D"] },
  D: { 0: [1, "L", "C"], 1: [1, "L", "F"] },
  E: { 0: [0, "L", "C"], 1: [0, "L", "B"] },
  F: { 0: [1, "L", "E"], 1: null },
};

const INITIAL_N =
  1975700577069254261393123959451562008800234946348086n;

// Exact arguments, in order, of the 107 A_step2 invocations in the
// pinned external Lean proof.
const ARGS = [
  13,21,5,5,21,5,17,21,5,27,35,21,5,5,21,5,5,31,21,5,
  5,21,5,17,21,5,5,21,5,5,21,21,21,5,5,21,5,5,21,5,
  5,31,21,5,5,21,21,21,5,5,21,5,27,39,21,5,5,21,5,5,
  31,21,5,5,21,5,17,21,5,5,21,5,5,21,21,21,5,5,21,5,
  5,21,5,5,31,21,5,5,21,5,17,21,5,5,21,5,5,21,21,21,
  5,5,21,5,5,21,5
];

const EXPECTED_BRANCH_WORD =
  "EEBBEBEEBEEEBBEBBEEBBEBEEBBEBBEEEBBEBBEBBEEBBEEEBBEBEEEBBEBBEEBBEBEEBBEBBEEEBBEBBEBBEEBBEBEEBBEBBEEEBBEBBEB";
const EXPECTED_FINAL_BRANCH = "E";

// Canonical suffix strings omit trailing blank zeros.  At call 50 the
// Lean list prints one extra trailing false; ListBlank identifies it
// with this canonical tape.
const CHECKPOINTS = [
  { call: 10, N: "35925965576050291197954676646168812866911688985763244505", suffix: "010101011" },
  { call: 20, N: "653274599173389056319717515476765122857837155218448003942322", suffix: "01011101010111" },
  { call: 30, N: "11879087870908968104360314522392758770461111276045783640742261386", suffix: "0111010111" },
  { call: 40, N: "216008289352335720339610602524813115320952275950623503089297980541682", suffix: "010110111" },
  { call: 50, N: "3927875740627220359664132971002588353805172690412603331883223229967369354", suffix: "01111111101" },
  { call: 60, N: "71424147101329785314496471805836819044114607618056461822634921267834080686730", suffix: "011011111111" },
  { call: 70, N: "1298770410781319861625359536628288369435308900216028055554241136144906066587587722", suffix: "011111101011111" },
  { call: 80, N: "23616726952692910182205306669292505610517611280824263889413609179834777358573759023858", suffix: "01011111011111" },
  { call: 90, N: "429444486360386240087203819295254784395458238425633310167425409595064063059982219052239602", suffix: "0100101011" },
  { call: 100, N: "7808980780222260203826248505306665087325883016528076661998155848237077485933315200811517542561", suffix: "0101011111111011" },
  { call: 107, N: "7488166283129708930486796847462680979065226437987146331898837006603604720521272903526417758309106", suffix: "01011011" },
];


const F7 = "0" + "1".repeat(6);
const Y3 = "01010111";
const E2_RESETS = [
  { call: 18, in: [0,2,F7], out: [0,6,Y3] },
  { call: 42, in: [0,2,"0111"], out: [0,6,"0101"] },
  { call: 54, in: [3,2,"01"], out: [0,8,"011111111"] },
  { call: 61, in: [0,2,"011111111"], out: [0,6,"0101011111"] },
  { call: 85, in: [0,2,"011111"], out: [0,6,"0101011"] },
];
function branchOf(N) {
  const r = Number(N % 3n);
  return ["A", "E", "B"][r];
}

function bitsToString(xs) {
  return xs.map(x => x ? "1" : "0").join("");
}

function regularSuffixParameters(s) {
  for (let q = 0; q <= Math.floor(s.length / 2); q++) {
    const prefix = "01".repeat(q);
    if (s.startsWith(prefix) && /^1*$/.test(s.slice(prefix.length))) {
      return { q, b: s.length - prefix.length };
    }
  }
  return null;
}


function packetSuffix(q, p, tail) {
  return "01".repeat(q) + "0" + "1".repeat(p) + tail;
}
function runAstep2(N, suffix, n) {
  const residue = Number(N % 3n);
  const q = N / 3n;
  const m = residue === 2 ? 4n * q + 3n : 4n * q - 1n;
  const extraZeros = residue === 0 ? 1 : residue === 1 ? 2 : 0;
  const branch = ["A", "E", "B"][residue];

  // Near-to-far left tape: 0^e, then the alternating block (10)^m,
  // then the two-cell base 11.  The huge block is represented by a
  // finite prefix plus its exact distance marker.
  const left = Array.from({ length: n + 64 }, (_, i) =>
    i < extraZeros ? 0 : ((i - extraZeros) % 2 === 0 ? 1 : 0)
  );
  const right = [...suffix, ...Array(n + 64).fill(0)];
  let state = branch;
  let displacement = 0; // #R - #L
  let marker = BigInt(extraZeros) + 2n * m + 1n;

  for (let i = 0; i < n; i++) {
    const transition = TM[state][right[0] ?? 0];
    if (transition === null || transition === undefined) {
      throw new Error(`halt during tail at primitive step ${i}, state ${state}`);
    }
    const [write, direction, nextState] = transition;
    right[0] = write;
    if (direction === "R") {
      left.unshift(write);
      right.shift();
      displacement += 1;
      marker += 1n;
    } else {
      const newHead = left.shift() ?? 0;
      right.unshift(newHead);
      right[1] = write;
      displacement -= 1;
      marker -= 1n;
    }
    state = nextState;
  }

  if (state !== "C") {
    throw new Error(`tail ended in ${state}, expected C (branch ${branch}, n=${n})`);
  }
  if (right[0] !== 1) {
    throw new Error(`tail ended on ${right[0]}, expected the first 1 of the block`);
  }
  if (marker <= BigInt(n + 4) || marker % 2n !== 0n) {
    throw new Error(`invalid alternating-block marker ${marker}`);
  }

  // Check every cell that the n-step tail could have disturbed, plus
  // four boundary cells.  The rest of the huge block is untouched.
  const inclusiveLeft = [right[0], ...left];
  const patternLimit = marker > BigInt(n + 4) ? n + 4 : Number(marker);
  for (let i = 0; i < patternLimit; i++) {
    const expected = i % 2 === 0 ? 1 : 0;
    if (inclusiveLeft[i] !== expected) {
      throw new Error(`alternating block mismatch at offset ${i}`);
    }
  }

  // side2 excludes the current head.  Count only its leading 1s.
  const side2 = right.slice(1);
  let z = 0;
  while (z < side2.length && side2[z] === 1) z++;
  const nextSuffix = side2.slice(z);
  while (nextSuffix.length > 0 && nextSuffix[nextSuffix.length - 1] === 0) {
    nextSuffix.pop();
  }

  // marker = 2*m' and the final two steps contribute two further 1s.
  const nextN = 2n + marker + BigInt(z);
  return {
    branch,
    displacement,
    leadingOnes: z,
    marker,
    nextN,
    nextSuffix,
  };
}

let N = INITIAL_N;
let suffix = [];
let branchWord = "";
const trace = [];
const checkpointMap = new Map(CHECKPOINTS.map(x => [x.call, x]));

for (let i = 0; i < ARGS.length; i++) {
  const inputSuffix = bitsToString(suffix);
  const out = runAstep2(N, suffix, ARGS[i]);
  branchWord += out.branch;
  N = out.nextN;
  suffix = out.nextSuffix;

  const row = {
    call: i + 1,
    branch: out.branch,
    n: ARGS[i],
    displacement: out.displacement,
    leadingOnes: out.leadingOnes,
    N: N.toString(),
    inputSuffix,
    suffix: bitsToString(suffix),
    regular: regularSuffixParameters(bitsToString(suffix)),
  };
  trace.push(row);

  const expected = checkpointMap.get(i + 1);
  if (expected) {
    if (N !== BigInt(expected.N)) {
      throw new Error(`N mismatch at call ${i + 1}: ${N} != ${expected.N}`);
    }
    if (bitsToString(suffix) !== expected.suffix) {
      throw new Error(`suffix mismatch at call ${i + 1}`);
    }
  }
}


const packetTrace = [];
const packetResets = [];
const e2ByCall = new Map(E2_RESETS.map(x => [x.call, x]));
let packetState = { q: 0, p: 8, tail: F7 };
if (trace[10].suffix !== packetSuffix(packetState.q, packetState.p, packetState.tail)) {
  throw new Error("call 11 did not produce the initial packet P(0,8;F7)");
}
packetTrace.push({ call: 11, ...packetState, suffix: trace[10].suffix });

const e0Calls = [];
const e2Calls = [];
for (let call = 12; call <= 107; call++) {
  const row = trace[call - 1];
  const inputState = { ...packetState };
  const priorN = BigInt(trace[call - 2].N);
  let nextState;
  let kind;
  let expectedN;

  if (row.branch === "B" && packetState.q > 0) {
    nextState = { q: packetState.q - 1, p: packetState.p, tail: packetState.tail };
    kind = "B";
    expectedN = 8n * ((priorN - 2n) / 3n) + 10n;
  } else if (row.branch === "E" && packetState.p >= 3) {
    nextState = { q: packetState.q + 2, p: packetState.p - 3, tail: packetState.tail };
    kind = "E";
    expectedN = 8n * ((priorN - 4n) / 3n) + 9n;
  } else if (row.branch === "E" && packetState.p === 0 && packetState.q > 0) {
    if (!packetState.tail.startsWith("01")) {
      throw new Error(`E0 input tail lacks 01 at call ${call}`);
    }
    nextState = { q: 0, p: 2 * packetState.q + 7, tail: packetState.tail.slice(2) };
    kind = "E0";
    expectedN = 8n * ((priorN - 4n) / 3n) + 5n;
    e0Calls.push(call);
  } else if (row.branch === "E" && packetState.p === 2) {
    const reset = e2ByCall.get(call);
    if (!reset || reset.in[0] !== packetState.q || reset.in[1] !== packetState.p || reset.in[2] !== packetState.tail) {
      throw new Error(`unclassified E2 reset at call ${call}`);
    }
    nextState = { q: reset.out[0], p: reset.out[1], tail: reset.out[2] };
    kind = "E2";
    expectedN = 8n * ((priorN - 4n) / 3n) + 5n;
    e2Calls.push(call);
  } else {
    throw new Error(`unclassified packet boundary at call ${call}`);
  }

  if (BigInt(row.N) !== expectedN) {
    throw new Error(`packet unary recurrence mismatch at call ${call} (${kind})`);
  }
  if (row.suffix !== packetSuffix(nextState.q, nextState.p, nextState.tail)) {
    throw new Error(`packet suffix mismatch at call ${call} (${kind})`);
  }
  packetState = nextState;
  packetTrace.push({ call, ...packetState, kind, suffix: row.suffix });
  if (kind === "E0" || kind === "E2") {
    packetResets.push({
      call, kind,
      input: inputState,
      output: packetState,
      unary: row.N,
    });
  }
}
if (JSON.stringify(e0Calls) !== JSON.stringify([24,32,47,67,75,91,99])) {
  throw new Error("unexpected E0 reset call sequence");
}
if (JSON.stringify(e2Calls) !== JSON.stringify([18,42,54,61,85])) {
  throw new Error("unexpected E2 reset call sequence");
}
if (packetState.q !== 1 || packetState.p !== 2 || packetState.tail !== "011") {
  throw new Error("unexpected final packet state");
}
if (ARGS.length !== 107) throw new Error("expected 107 macro calls");
if (branchWord !== EXPECTED_BRANCH_WORD) throw new Error("branch word mismatch");
if (branchOf(N) !== EXPECTED_FINAL_BRANCH) throw new Error("final branch mismatch");

const result = {
  sourceCommit: "1929f57df4dd7afcc11c3f458e20526fd1f991e0",
  macroCalls: ARGS.length,
  branchWord,
  finalBranch: branchOf(N),
  checkpoints: CHECKPOINTS,
  packetTrace,
  packetResets,
  finalPacket: packetTrace[packetTrace.length - 1],
  firstEleven: trace.slice(0, 11),
  finalN: N.toString(),
  finalSuffix: bitsToString(suffix),
  allTailAndBlockChecksPassed: true,
};

if (process.argv.includes("--trace")) {
  console.log(JSON.stringify(trace, null, 2));
} else {
  console.log(JSON.stringify(result, null, 2));
}
