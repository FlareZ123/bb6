// Exact modular reproduction of the seven-edge nested odd-parent branch.
// All exponentiation is modular BigInt; no full 2^n integer is constructed.
const mod = (x, m) => ((x % m) + m) % m;
function powMod(base, exp, modulus) {
  let x = base % modulus, e = exp, out = 1n;
  while (e > 0n) {
    if ((e & 1n) !== 0n) out = (out * x) % modulus;
    x = (x * x) % modulus;
    e >>= 1n;
  }
  return out;
}
const p3 = k => 3n ** BigInt(k);

function computeAt(r) {
  const n = 887n + 13122n * r;
  const qmod = mod(
    28n * powMod(2n, n, p3(20))
      - 2n * n + 15n
      - powMod(2n, 3406n, p3(20)) * (2n * n + 3n),
    p3(20)
  );
  const d1 = qmod / p3(10);
  const g1 = mod(
    512n * d1 - 16n * powMod(2n, n - 7n, p3(10))
      - 2n * (n - 7n) - 5n,
    p3(10)
  );
  const d2 = g1 / p3(2);
  const g2 = mod(
    8n * d2 - 16n * powMod(2n, n - 8n, p3(8))
      - 2n * (n - 8n) - 5n,
    p3(8)
  );
  const d3 = g2 / 3n;
  const g3 = mod(
    4n * d3 - 16n * powMod(2n, n - 9n, p3(7))
      - 2n * (n - 9n) - 5n,
    p3(7)
  );
  const d4 = g3 / 27n;
  const g4 = mod(
    16n * d4 - 16n * powMod(2n, n - 11n, p3(4))
      - 2n * (n - 11n) - 5n,
    p3(4)
  );
  const d5 = g4 / 9n;
  const g5 = mod(
    8n * d5 - 16n * powMod(2n, n - 12n, p3(2))
      - 2n * (n - 12n) - 5n,
    p3(2)
  );
  const d6 = g5 / 3n;
  const g6 = mod(
    4n * d6 - 16n * powMod(2n, n - 13n, 3n)
      - 2n * (n - 13n) - 5n,
    3n
  );
  return {r,n,qmod,g1,g2,g3,g4,g5,g6};
}

const r = 74803n;
const main = computeAt(r);
const {n,qmod,g1,g2,g3,g4,g5,g6} = main;
if (qmod % p3(10) !== 0n || qmod % p3(11) === 0n) {
  throw new Error("Q does not have exact 3-adic valuation 10");
}
if (g1 % 9n !== 0n || g1 % 27n === 0n) {
  throw new Error("G1 does not have exact 3-adic valuation 2");
}
if (g2 % 3n !== 0n || g2 % 9n === 0n) {
  throw new Error("G2 does not have exact 3-adic valuation 1");
}
if (g3 % p3(5) !== 0n || g3 % p3(6) === 0n) {
  throw new Error("G3 does not have exact 3-adic valuation 5");
}
if (g4 % 9n !== 0n || g4 % 27n === 0n) {
  throw new Error("G4 does not have exact 3-adic valuation 2");
}
if (g5 % 3n !== 0n || g5 % 9n === 0n) {
  throw new Error("G5 does not have exact 3-adic valuation 1");
}
if (g6 !== 0n) throw new Error("G6 is not divisible by 3");

// The three lifts of r=74803 mod 3^11 to mod 3^12.
// Exactly the first makes G6 divisible by 3.
const nextDigitResidues = [0n,1n,2n].map(a =>
  computeAt(r + p3(11) * a).g6.toString()
);
if (nextDigitResidues.join(",") !== "0,2,1") {
  throw new Error("Unexpected next-digit G6 residues");
}

// Coefficients X_i=A_i*2^n+B_i*n+C_i through X_6.
// X_6 supplies the linear/constant error bound for the seventh band.
const bitLength = x => (x < 0n ? -x : x).toString(2).length;
const coefficientBits = [];
let B = -2n - (1n << 3407n);
let C = 15n - 3n * (1n << 3406n);
coefficientBits.push({level:0,B:bitLength(B),C:bitLength(C)});
let E = 0;
const stages = [[7,14],[1,9],[0,9],[2,13],[1,13],[0,13]];
for (let i=0;i<stages.length;i++) {
  const [t,sigma] = stages[i];
  E = i===0 ? t+3 : E+t+1;
  B = 4n*(1n<<BigInt(t))*B - 2n*p3(E);
  C = 4n*(1n<<BigInt(t))*C
    - (2n*BigInt(t-sigma)+5n)*p3(E);
  coefficientBits.push({level:i+1,B:bitLength(B),C:bitLength(C)});
}
if (coefficientBits.some(x => x.B > 3431 || x.C > 3431)) {
  throw new Error("Unexpected coefficient bound for the seven band estimates");
}

const limitingRatios = [
  [458752n,59049n],
  [3560896n,531441n],
  [11481056n,1594323n],
  [326640896n,43046721n],
  [2471264192n,387420489n],
  [7372657888n,1162261467n],
  [21788896160n,3486784401n]
];
for (const [num,den] of limitingRatios) {
  if (5n*num <= 31n*den || 10n*num >= 79n*den) {
    throw new Error("A limiting band ratio is outside (6.2,7.9)");
  }
}
const bandParameters = [[7,14],[1,9],[0,9],[2,13],[1,13],[0,13],[0,14]];
for (const [t,sigma] of bandParameters) {
  if ((1n<<BigInt(sigma)) >= p3(t+1)*8192n) {
    throw new Error("A band scaling factor is not below 2^13");
  }
}
if (n < 7000n) throw new Error("The explicit index is below the band-bound threshold");

console.log(JSON.stringify({
  r:r.toString(),
  classModulus:"531441",
  n:n.toString(),
  valuations:{Q:10,G1:2,G2:1,G3:5,G4:2,G5:1,G6:"divisible by 3"},
  nextDigitResidues,
  exponents:bandParameters,
  coefficientBitLengths:coefficientBits,
  limitingBandRatios:limitingRatios.map(([num,den])=>({num:num.toString(),den:den.toString()})),
  bandBound:"for n >= 7000, all seven normalized ratios differ from their limits by < 2^-55"
},null,2));
