// Exact BigInt reconnaissance for the five-shallow finite core.
// This is experimental evidence, not a Lean proof. It checks the natural
// equation from FiveShallowIntegerAlgebra for 14 <= n <= 82, s <= 3,
// all five profile bits, and u,v,w,x,r <= 2, restricted by the root divisor.
// It deliberately omits additional source-time inequalities, so the scanned
// set is a superset of the admissible source cases.

"use strict";

const pow = (a, b) => BigInt(a) ** BigInt(b);
const profile = (t) =>
  t === 0
    ? { alpha: 1n, C: 588n, L: 84n, O: 232n }
    : { alpha: 2n, C: 392n, L: 56n, O: 136n };

let rootPairs = 0;
let boundedAssignments = 0;
let nonnegativeAssignments = 0;
const solutions = [];

for (let n = 14; n <= 82; n++) {
  const N = BigInt(n);
  const twoN = pow(2, n);
  const D = 14n * N + 92n;

  for (let s = 0; s <= 3; s++) {
    const q = pow(8, s);
    if (D % q !== 0n) continue;

    rootPairs++;
    const p = twoN / q;
    const d = D / q;

    for (let mask = 0; mask < 32; mask++) {
      const P = Array.from({ length: 5 }, (_, i) =>
        profile((mask >> i) & 1)
      );
      const [P1, P2, P3, P4, P5] = P;

      for (let u = 0; u <= 2; u++)
      for (let v = 0; v <= 2; v++)
      for (let w = 0; w <= 2; w++)
      for (let x = 0; x <= 2; x++)
      for (let r = 0; r <= 2; r++) {
        boundedAssignments++;

        const A1 = pow(2, P1.alpha) * pow(8, u);
        const A2 = pow(2, P2.alpha) * pow(8, v);
        const A3 = pow(2, P3.alpha) * pow(8, w);
        const A4 = pow(2, P4.alpha) * pow(8, x);
        const A5 = pow(2, P5.alpha) * pow(8, r);

        const T1 = N + 6n + 3n * BigInt(s);
        const R1 = P1.L * T1 - P1.O - d;

        const T2 = T1 + P1.alpha + 3n * BigInt(u);
        const R2 = P2.L * T2 - P2.O;

        const T3 = T2 + P2.alpha + 3n * BigInt(v);
        const R3 = P3.L * T3 - P3.O;

        const T4 = T3 + P3.alpha + 3n * BigInt(w);
        const R4 = P4.L * T4 - P4.O;

        const T5 = T4 + P4.alpha + 3n * BigInt(x);
        const R5 = P5.L * T5 - P5.O;

        const T6 = T5 + P5.alpha + 3n * BigInt(r);
        const E = 112n * T6 - 384n;

        // Keep even zero remainders: this intentionally enlarges the
        // admissible source domain, whose profile theorem gives strict >0.
        if ([R1, R2, R3, R4, R5, E].some((z) => z < 0n)) continue;
        nonnegativeAssignments++;

        const K =
          P1.C * q +
          P2.C * q * A1 +
          P3.C * q * A1 * A2 +
          P4.C * q * A1 * A2 * A3 +
          P5.C * q * A1 * A2 * A3 * A4 -
          98n;

        const lhs = K * p;
        const rhs =
          A1 *
            (A2 *
              (A3 *
                (A4 * (A5 * E + R5) + R4) +
                R3) +
              R2) +
          R1;

        if (lhs === rhs) {
          solutions.push({
            n, s, mask, u, v, w, x, r,
            remainders: [R1, R2, R3, R4, R5].map(String),
            E: String(E),
            K: String(K),
          });
        }
      }
    }
  }
}

const summary = {
  nRange: [14, 82],
  rootCompatiblePairs: rootPairs,
  boundedAssignments,
  nonnegativeAssignments,
  solutionCount: solutions.length,
  firstSolutions: solutions.slice(0, 20),
};

console.log(JSON.stringify(summary, null, 2));

// Expected exact output for this version:
// rootCompatiblePairs = 90
// boundedAssignments = 699840
// nonnegativeAssignments = 699840
// solutionCount = 0
