// Independent exact digit-word count of full-rectangle synchronization.
// Node.js: node count_sync_words.js
// This finite reproducer corroborates but does not prove the all-n formula.
const mod = (a, m) => ((a % m) + m) % m;
const subset = (mask, bits) => (mask & bits) === mask;
for (let n = 2; n <= 7; ++n) {
  const M = 3 ** n, N = M / 3;
  const counts = Array(16).fill(0);
  let accepted = 0;
  for (let U = 0; U < M; ++U) {
    for (let V = 0; V < M; ++V) {
      const a = mod(V - 4*U, M), c = mod(4*V - U, M);
      const bits = (a <= 3 || a >= M-2 ? 1 : 0)
        | (c <= 1 || c >= M-7 ? 2 : 0)
        | (U % N === 0 || U % N === N-1 ? 4 : 0)
        | (V % N === 0 || V % N === N-1 || V % N === N-2 ? 8 : 0);
      if (bits === 0) ++accepted;
      for (let mask = 1; mask < 16; ++mask) {
        if (subset(mask, bits)) ++counts[mask];
      }
    }
  }
  const polynomial = M*M-30*M+291;
  const singles = [1,2,4,8].map(m => counts[m]);
  const pairs = [3,5,9,6,10,12].map(m => counts[m]);
  const triples = [7,11,13,14].map(m => counts[m]);
  const quadruple = counts[15];
  console.log(JSON.stringify({n, M, accepted, polynomial, 
    matches_for_n_ge_4: n < 4 ? null : accepted === polynomial,
    singles, pairs, triples, quadruple}));
  if (n >= 4 && accepted !== polynomial) process.exitCode = 1;
}
