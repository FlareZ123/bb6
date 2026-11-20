#!/usr/bin/env node
// Three-state transducer for N=(2b-1+3^L)/4.
// Input ternary digits are read least-significant first.
const table = [
  [[2, 1], [1, 0], [0, 2]], // A
  [[0, 0], [2, 1], [1, 0]], // B
  [[1, 0], [0, 2], [2, 0]], // C
];

function depth(b) {
  const x = 2n * b - 1n;
  for (let L = 1; ; L++) {
    if (BigInt(L % 2) === b % 2n &&
        3n ** BigInt(L - 1) <= x &&
        x < 3n ** BigInt(L + 1)) return L;
  }
}

function transduce(b) {
  const L = depth(b);
  let state = 0; // A
  let x = b, N = 0n, place = 1n;
  let R = 0, e = 0, Delta = 0, lastOut = -1;
  for (let i = 0; i < L; i++) {
    const digit = Number(x % 3n);
    x /= 3n;
    const [out, next] = table[state][digit];
    state = next;
    lastOut = out;
    N += BigInt(out) * place;
    place *= 3n;
    if (out !== 0) R++;
    if (out === 2) e++;
    if (out === 1) Delta++;
    if (out === 2) Delta--;
  }
  return {L, N, R, e, Delta, state, lastOut};
}

let tested = 0, maxL = 0;
for (let b = 1n; b <= 10000n; b++) {
  const z = transduce(b);
  const expected = (2n * b - 1n + 3n ** BigInt(z.L)) / 4n;
  if (z.N !== expected) throw new Error(`N mismatch at b=${b}`);
  if (4n * z.N !== 2n * b - 1n + 3n ** BigInt(z.L))
    throw new Error(`identity mismatch at b=${b}`);
  const expectedTerminal = b < 3n ** BigInt(z.L) ? 0 : 1;
  if (z.state !== expectedTerminal)
    throw new Error(`terminal state mismatch at b=${b}`);
  if (z.lastOut === 0) throw new Error(`zero leading digit at b=${b}`);
  tested++;
  if (z.L > maxL) maxL = z.L;
}
process.stdout.write(JSON.stringify({tested, maxL, states: 3, mismatches: 0}) + "\n");
