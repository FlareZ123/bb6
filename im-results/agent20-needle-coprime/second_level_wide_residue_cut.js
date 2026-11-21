#!/usr/bin/env node
"use strict";

// Exact audit for SecondLevelWideResidueCut.md.
// Usage: node second_level_wide_residue_cut.js [r] [--details]
// r must be 110*j+50. All mathematical arithmetic is BigInt.

function mod(x, m) {
  return ((x % m) + m) % m;
}

function powMod(base, exponent, modulus) {
  let x = mod(base, modulus);
  let e = exponent;
  let out = 1n;
  while (e > 0n) {
    if ((e & 1n) !== 0n) out = (out * x) % modulus;
    x = (x * x) % modulus;
    e >>= 1n;
  }
  return out;
}

// Compute y mod m exactly from 55*y = 8*A*P_r(A)+25.
// Work modulo 55*m so division by 55 is exact after taking the residue.
function yMod(r, a, m) {
  const modulus = 55n * m;
  const A = powMod(2n, a, modulus);
  const A2 = (A * A) % modulus;
  let P = 0n;
  let ninePower = 1n;
  for (let i = 0n; i < r; i++) {
    P = mod(A2 * P + ninePower * (A - 3n), modulus);
    ninePower = (ninePower * 9n) % modulus;
  }
  const numerator = mod(8n * A * P + 25n, modulus);
  if (numerator % 55n !== 0n) {
    throw new Error("The target numerator is not divisible by 55 modulo 55*m.");
  }
  return numerator / 55n;
}

function isOddEntry(w, j) {
  const r20 = mod(w, 20n);
  return r20 === 1n || r20 === 2n || r20 === 15n ||
    mod(w, 100n) === mod(64n - 40n * j, 100n);
}

function isLongOddBlock(w, j) {
  return mod(w, 100n) === mod(61n - 40n * j, 100n) ||
    mod(w, 100n) === mod(2n + 60n * j, 100n) ||
    mod(w, 100n) === mod(95n - 40n * j, 100n) ||
    mod(w, 500n) === mod(464n + 260n * j, 500n);
}

function analyze(r, details) {
  if (r < 50n || mod(r - 50n, 110n) !== 0n) {
    throw new Error("Require r = 110*j+50 with j >= 0.");
  }

  const j = (r - 50n) / 110n;
  const a = (9n ** r + 5n) / 2n;
  const n = 3n ** (2n * r - 1n);
  const d = BigInt(n.toString(2).length);

  const bandLo = (a + 2n * r - 2n) / (2n * r - 1n);
  const bandHi = (a - d - 3n) / (r - 1n);
  const bandCount = bandHi >= bandLo ? bandHi - bandLo + 1n : 0n;

  const primes = [5n, 7n, 11n, 13n, 19n, 29n, 37n, 61n, 67n, 79n, 101n];
  const yPrime = new Map();
  for (const p of primes) yPrime.set(p.toString(), yMod(r, a, p));

  const smallT = [];
  const yT = new Map();
  const DT = new Map();
  for (let t = 1n; t <= 7n; t++) {
    const D = (2n ** (t + 1n)) + 3n;
    DT.set(t.toString(), D);
    yT.set(t.toString(), yMod(r, a, D));
  }

  const candidates = [];
  for (let k = r - 1n; k <= 2n * r - 2n; k++) {
    for (let e = 0n; e <= d - 2n; e++) {
      const numerator = a - 5n - e;
      if (numerator % k !== 0n) continue;
      const s = numerator / k;
      if ((2n * r - 1n) * s < a) continue;
      if ((r - 1n) * s > a - d - 3n) continue;

      // Here c(s)=e+1<d, so this is one of the theorem's
      // explicitly enumerable residue-cut exceptions.
      const w = a + s - 1n;

      let primePass = true;
      let failedPrime = null;
      for (const p of primes) {
        const Dmod = mod(powMod(2n, w + 1n, p) + 3n, p);
        if (Dmod === 0n) {
          const beta = mod(3n * powMod(2n, w, p) + w + 3n, p);
          if (yPrime.get(p.toString()) !== beta) {
            primePass = false;
            failedPrime = p;
            break;
          }
        }
      }

      const oddEntry = isOddEntry(w, j);
      const longOddBlock = isLongOddBlock(w, j);
      const evenTs = [];
      const oddTs = [];

      for (let t = 1n; t <= 7n; t++) {
        const D = DT.get(t.toString());
        const y = yT.get(t.toString());

        const H = mod(
          powMod(2n, w + 2n, D) * (y + 3n - w - t) + 9n - 6n * t,
          D
        );
        if (H === 0n) evenTs.push(Number(t));

        const J = mod(
          powMod(2n, w + 1n, D) * (4n * y - 4n * w + 27n - 10n * t) +
            63n - 30n * t,
          D
        );
        if (J === 0n) oddTs.push(Number(t));
      }

      candidates.push({
        k: k,
        e: e,
        s: s,
        w: w,
        primePass: primePass,
        failedPrime: failedPrime,
        oddEntry: oddEntry,
        longOddBlock: longOddBlock,
        evenTs: evenTs,
        oddTs: oddTs
      });
    }
  }

  const primeSurvivors = candidates.filter(x => x.primePass);
  const forcedEven = primeSurvivors.filter(x => !x.oddEntry);
  const oddEntry = primeSurvivors.filter(x => x.oddEntry);
  const oddShort = oddEntry.filter(x => !x.longOddBlock);

  const summary = {
    r: r.toString(),
    j: j.toString(),
    a: a.toString(),
    d: Number(d),
    band: {
      s_min: bandLo.toString(),
      s_max: bandHi.toString(),
      number_of_s: bandCount.toString()
    },
    exception_bound: (r * (d - 1n)).toString(),
    exact_exception_count: candidates.length,
    after_eleven_prime_filter: primeSurvivors.length,
    forced_even_survivors: forcedEven.length,
    forced_even_with_some_t_1_to_7: forcedEven.filter(x => x.evenTs.length > 0).length,
    forced_even_with_no_t_1_to_7: forcedEven.filter(x => x.evenTs.length === 0).length,
    odd_entry_survivors: oddEntry.length,
    long_odd_block_survivors: oddEntry.filter(x => x.longOddBlock).length,
    short_odd_block_survivors: oddShort.length,
    short_odd_with_some_t_1_to_7: oddShort.filter(x => x.oddTs.length > 0).length,
    short_odd_with_no_t_1_to_7: oddShort.filter(x => x.oddTs.length === 0).length
  };

  if (details) {
    summary.survivors = primeSurvivors.map(x => ({
      k: x.k.toString(),
      e: x.e.toString(),
      s: x.s.toString(),
      w: x.w.toString(),
      oddEntry: x.oddEntry,
      longOddBlock: x.longOddBlock,
      evenTs: x.evenTs,
      oddTs: x.oddTs
    }));
  }

  return summary;
}

const args = process.argv.slice(2);
const r = BigInt(args.find(x => !x.startsWith("--")) || "50");
const details = args.includes("--details");
const result = analyze(r, details);
process.stdout.write(JSON.stringify(result, null, 2) + "\n");
