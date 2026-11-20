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
      throw new Error(\`halt during tail at primitive step \${i}, state \${state}\`);
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
    throw new Error(\`tail ended in \${state}, expected C (branch \${branch}, n=\${n})\`);
  }
  if (right[0] !== 1) {
    throw new Error(\`tail ended on \${right[0]}, expected the first 1 of the block\`);
  }
  if (marker <= 0n || marker % 2n !== 0n) {
    throw new Error(\`invalid alternating-block marker \${marker}\`);
  }

  // Check every cell that the n-step tail could have disturbed, plus
  // four boundary cells.  The rest of the huge block is untouched.
  const inclusiveLeft = [right[0], ...left];
  const patternLimit = marker > BigInt(n + 4) ? n + 4 : Number(marker);
  for (let i = 0; i < patternLimit; i++) {
    const expected = i % 2 === 0 ? 1 : 0;
    if (inclusiveLeft[i] !== expected) {
      throw new Error(\`alternating block mismatch at offset \${i}\`);
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
      throw new Error(\`N mismatch at call \${i + 1}: \${N} != \${expected.N}\`);
    }
    if (bitsToString(suffix) !== expected.suffix) {
      throw new Error(\`suffix mismatch at call \${i + 1}\`);
    }
  }
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
