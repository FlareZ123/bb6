// Exact modular certificate for the rho-20 q=0 phases a = 14,32 (mod 54).
// The accompanying proof note establishes the period reduction for all lifts.
function powMod(base, exponent, modulus) {
  let result = 1n;
  base %= modulus;
  while (exponent > 0n) {
    if (exponent & 1n) result = (result * base) % modulus;
    base = (base * base) % modulus;
    exponent >>= 1n;
  }
  return result;
}
const mod = (x, m) => ((x % m) + m) % m;
const expected = {
  14: [
    [14, 71, 152, 142, 229, 73, 196, 44, 162, 108, 6, 189, 2],
    [68, 233, 152, 88, 229, 235, 115, 206, 162, 108, 6, 189, 2],
    [122, 152, 152, 34, 229, 154, 34, 125, 162, 108, 6, 189, 2],
  ],
  32: [
    [32, 44, 44, 16, 67, 208, 169, 17, 81, 27, 6, 108, 1],
    [86, 206, 44, 124, 67, 127, 88, 179, 81, 27, 6, 108, 1],
    [140, 125, 44, 70, 67, 46, 7, 98, 81, 27, 6, 108, 1],
  ],
};
for (const phase of [14n, 32n]) {
  const rows = [];
  for (let n = 0n; n < 3n; n++) {
    const a = phase + 54n * n;
    const e = a - 7n;
    const K243 = mod(97n * powMod(2n, e, 243n) + 48n, 243n);
    const K162 = mod(97n * powMod(2n, e, 162n) + 48n, 162n);
    const r162 = mod(K162 + 4n - a, 162n);
    const p243 = powMod(2n, K162, 243n);
    const q243 = powMod(2n, mod(K162 - a, 162n), 243n);
    const r243 = powMod(2n, r162, 243n);
    const B243 = mod((2n * K243 + 7n) * r243, 243n);
    const threeX243 = mod(80n * p243 + 2n * K243 + 13n - 2n * B243, 243n);
    const nineX1_243 = mod(248n * p243 - 8n * B243 - 10n * K243 + 25n, 243n);
    const A9 = mod(4n * p243 + 2n * K243 + 1n, 9n);
    const Gnum243 = mod(26368n * q243 + 74n * K243 - 23n, 243n);
    const Xmod81 = threeX243 / 3n;
    const sideZ3 = mod(16n * (Xmod81 / 27n) - 4n * p243 - 2n * K243 - 1n, 3n);
    const row = [a, K243, K162, r162, p243, q243, r243, B243,
      threeX243, nineX1_243, A9, Gnum243, sideZ3].map(Number);
    rows.push(row);
  }
  const want = expected[Number(phase)];
  if (JSON.stringify(rows) !== JSON.stringify(want)) {
    throw new Error(`phase ${phase}: ${JSON.stringify(rows)}`);
  }
  console.log(`phase ${phase}: ${JSON.stringify(rows)}`);
}
console.log("All six exact modular rows agree.");
