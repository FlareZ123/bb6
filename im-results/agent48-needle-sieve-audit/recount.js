"use strict";

const c7 = [6, 3, 1];
const gcd = (a, b) => b === 0n ? a : gcd(b, a % b);
const mod = (a, m) => ((a % m) + m) % m;
const fraction = (n, d) => {
  const g = gcd(n, d);
  return `${n / g}/${d / g}`;
};
const bad5 = w => w % 4 === 0 && w % 5 !== 4;

function countEight(j) {
  let total = 0n;
  const c11 = mod(9 - j, 11);
  for (let w = 0; w < 13860; w++) {
    if (bad5(w) || w % 12 === 9) continue;
    if (w % 3 === 1 && w % 7 !== c7[j % 3]) continue;
    if (w % 10 === 2 && w % 11 !== c11) continue;
    const active = [
      w % 18 === 3,
      w % 28 === 18,
      w % 60 === 35,
      w % 66 === 5,
    ];
    const primes = [19n, 29n, 61n, 67n];
    let ways = 1n;
    for (let i = 0; i < primes.length; i++) ways *= active[i] ? 1n : primes[i];
    total += ways;
  }
  return total;
}

function countEleven(j) {
  let total = 0n;
  const c11 = mod(9 - j, 11);
  for (let w = 0; w < 900900; w++) {
    if (bad5(w) || w % 12 === 9) continue;
    if (w % 3 === 1 && w % 7 !== c7[j % 3]) continue;
    if (w % 10 === 2 && w % 11 !== c11) continue;
    const active = [
      w % 18 === 3,
      w % 28 === 18,
      w % 36 === 7,
      w % 60 === 35,
      w % 66 === 5,
      w % 39 === 9,
      w % 100 === 18,
    ];
    const primes = [19n, 29n, 37n, 61n, 67n, 79n, 101n];
    let ways = 1n;
    for (let i = 0; i < primes.length; i++) ways *= active[i] ? 1n : primes[i];
    total += ways;
  }
  return total;
}

function count121(j) {
  let total = 0n;
  const c11 = mod(9 - j, 11);
  for (let w = 0; w < 152460; w++) {
    if (bad5(w) || w % 12 === 9) continue;
    if (w % 3 === 1 && w % 7 !== c7[j % 3]) continue;
    if (w % 10 === 2 && w % 11 !== c11) continue;
    if (w % 110 === 32) {
      if (j % 11 !== 10) continue;
      const t = (j - 10) / 11;
      if (w % 121 !== mod(76 - 11 * t, 121)) continue;
    }
    const active = [
      w % 18 === 3,
      w % 28 === 18,
      w % 60 === 35,
      w % 66 === 5,
    ];
    const primes = [19n, 29n, 61n, 67n];
    let ways = 1n;
    for (let i = 0; i < primes.length; i++) ways *= active[i] ? 1n : primes[i];
    total += ways;
  }
  return total;
}

const m8 = 13860n * 19n * 29n * 61n * 67n;
const m11 = 900900n * 19n * 29n * 37n * 61n * 67n * 79n * 101n;
const m121 = 152460n * 19n * 29n * 61n * 67n;

const eight = Array.from({length: 33}, (_, j) => countEight(j));
const eleven = Array.from({length: 33}, (_, j) => countEleven(j));
const primeSquare = Array.from({length: 121}, (_, j) => count121(j));
if (new Set(eight.map(String)).size !== 1) throw new Error("eight-prime count varies with j");
if (new Set(eleven.map(String)).size !== 1) throw new Error("eleven-prime count varies with j");
if (new Set(primeSquare.filter((_, j) => j % 11 !== 10).map(String)).size !== 1)
  throw new Error("11^2 baseline varies with j");
if (new Set(primeSquare.filter((_, j) => j % 11 === 10).map(String)).size !== 1)
  throw new Error("11^2 refinement varies with j");

const n8 = eight[0], n11 = eleven[0];
const n121Base = primeSquare[0], n121Refined = primeSquare[10];
console.log("eight-prime", n8.toString(), "/", m8.toString(), fraction(n8, m8), Number(n8) / Number(m8));
console.log("eleven-prime", n11.toString(), "/", m11.toString(), fraction(n11, m11), Number(n11) / Number(m11));
console.log("11^2 baseline", n121Base.toString(), "/", m121.toString(), fraction(n121Base, m121), Number(n121Base) / Number(m121));
console.log("11^2 refined", n121Refined.toString(), "/", m121.toString(), fraction(n121Refined, m121), Number(n121Refined) / Number(m121));
console.log("w=24 survives all listed cylinders:", !bad5(24) && 24 % 12 !== 9 &&
  !(24 % 3 === 1 && 24 % 7 !== c7[0]) && !(24 % 10 === 2 && 24 % 11 !== mod(9, 11)) &&
  24 % 18 !== 3 && 24 % 28 !== 18 && 24 % 36 !== 7 && 24 % 60 !== 35 &&
  24 % 66 !== 5 && 24 % 39 !== 9 && 24 % 100 !== 18 && 24 % 110 !== 32);
