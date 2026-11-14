// Exact r=50 endpoints for the large-remainder quotient-band theorem.
"use strict";
const r = 50n;
const a = (9n ** r + 5n) / 2n;
function bitLength(n) { return BigInt(n.toString(2).length); }
function mod(n,m) { return ((n % m) + m) % m; }

for (let k = 0n; k <= 6n; k++) {
  const m = k + 1n;
  let d0 = mod(-a, m);
  if (d0 === 0n) d0 = m;
  const tMax = (a - d0) / m;
  function admissible(t) {
    const d = d0 + m * t;
    const w = (a + d) / m - 1n;
    const E = w - 2n * r * d;
    return d <= w &&
      E >= bitLength(110n * w) &&
      E >= bitLength(32n * r) + 4n * r * m;
  }
  let lo = 0n, hi = tMax + 1n;
  while (lo + 1n < hi) {
    const mid = (lo + hi) / 2n;
    if (admissible(mid)) lo = mid;
    else hi = mid;
  }
  if (!admissible(0n)) continue;
  const dLast = d0 + m * lo;
  const wMin = (a + d0) / m - 1n;
  const wMax = (a + dLast) / m - 1n;
  console.log({k:k.toString(),dFirst:d0.toString(),dLast:dLast.toString(),
    wMin:wMin.toString(),wMax:wMax.toString(),count:(lo+1n).toString()});
}
