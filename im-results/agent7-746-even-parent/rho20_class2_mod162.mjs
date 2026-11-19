// Exact modular certificate for a = 38 + 54 n in the rho-20 residual class.
// The three-row period table, rather than a finite sample, is the proof basis.
function powMod(base, exponent, modulus) {
  let x = 1n, b = base % modulus, e = exponent;
  while (e > 0n) {
    if ((e & 1n) !== 0n) x = (x * b) % modulus;
    b = (b * b) % modulus;
    e >>= 1n;
  }
  return x;
}
const mod = (x, m) => ((x % m) + m) % m;
const rows = [];
for (let n = 0n; n < 12n; n++) {
  const a = 38n + 54n * n;
  const twoA243 = powMod(2n, a - 7n, 243n);
  const twoA162 = powMod(2n, a - 7n, 162n);
  const K243 = mod(97n * twoA243 + 48n, 243n);
  const K162 = mod(97n * twoA162 + 48n, 162n);
  const r162 = mod(K162 + 4n - (a % 162n), 162n);
  const p243 = powMod(2n, K162, 243n);
  const q243 = powMod(2n, mod(K162 - (a % 162n), 162n), 243n);
  const r243 = powMod(2n, r162, 243n);
  const B243 = mod((2n * K243 + 7n) * r243, 243n);
  const Xnum81 = mod(
    80n * (p243 % 81n) + 2n * (K243 % 81n) + 13n - 2n * (B243 % 81n),
    81n
  );
  const X1num243 = mod(248n * p243 - 8n * B243 - 10n * K243 + 25n, 243n);
  const Amod9 = mod(4n * (p243 % 9n) + 2n * (K243 % 9n) + 1n, 9n);
  const Gnum243 = mod(26368n * q243 + 74n * K243 - 23n, 243n);
  if (K162 !== 116n || p243 !== 175n ||
      Xnum81 !== 54n || X1num243 !== 81n ||
      Amod9 !== 6n || Gnum243 !== 0n) {
    throw new Error("rho-20 class-2 modular certificate failed at n=" + n);
  }
  rows.push({
    n: String(n), a: String(a),
    K243: String(K243), K162: String(K162), r162: String(r162),
    p243: String(p243), q243: String(q243), r243: String(r243),
    B243: String(B243), Xnum81: String(Xnum81),
    Xmod27: String(Xnum81 / 3n), X1num243: String(X1num243),
    X1mod27: String(X1num243 / 9n), Amod9: String(Amod9),
    Gnum243: String(Gnum243)
  });
}
process.stdout.write(JSON.stringify(rows, null, 2) + "\n");
