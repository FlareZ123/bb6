// Independent BigInt transcription of the pinned Agent49ParitySource recurrence.
// This is a reproducible search, not a proof. Run with: node scan_terminal_budget_family.js

function evalA(a, k, m) {
  while (true) {
    if (k % 3n === 2n) return [a + 1n, k / 3n, m];
    if (a === 0n) return k % 3n === 0n ? null : [0n, k / 3n, m];
    if (k % 3n === 0n) return [a - 1n, k / 3n, m + 2n];
    k = k / 3n;
    m = m + 2n * k + 3n;
    a--;
  }
}

function drainB(a, b, d) {
  while (b !== 0n) {
    const p = evalA(a, b - 1n, d + 2n * b + 3n);
    if (!p || p[1] >= b) return null;
    [a, b, d] = p;
  }
  return [a, d];
}

function next(a, d) {
  if (a === 0n) return d % 2n === 1n ? drainB(d + 1n, 2n, 2n) : [d, 7n];
  if (d % 2n === 1n && a >= d + 5n) return drainB(a - d - 5n, d + 3n, 5n);
  if (d % 2n === 0n && a >= d + 3n) return drainB(a - d - 2n, d + 2n, 2n);
  if (a % 2n === 1n) return null;
  if (a === d + 2n) return drainB(0n, a, 2n);
  if (d % 2n === 1n) return drainB(d + 4n - a, a - 1n, 3n);
  const p = evalA(d + 1n - a, a, 2n * a + 5n);
  return p ? drainB(...p) : null;
}

const hits = [];
for (let d = 19681; d <= 24819; d += 2) {
  const D = BigInt(d);
  for (let offset = -455; offset <= 445; offset += 2) {
    const a = 13n * D + BigInt(offset);
    if (a % 2n !== 0n || a < 9n * D + 55n) continue;
    if (14n * D + 59n > 3n ** 16n) continue;
    const p = next(a, D);
    if (!p) continue;
    const [pa, pd] = p;
    if (pd % 2n !== 1n || pa < pd + 5n) continue;
    const h = next(pa, pd);
    if (!h || next(...h) !== null) continue;
    const ratioGap = pa - 4n * pd;
    if (ratioGap < -115n || ratioGap > 115n) continue;
    const bridgeError = ratioGap - 5n - (a - 13n * D);
    if (bridgeError < -306n || bridgeError > 306n) continue;
    hits.push({ d, a, offset, mass: a + D, p, h, ratioGap, bridgeError });
  }
}

hits.sort((x, y) => x.mass < y.mass ? -1 : x.mass > y.mass ? 1 : 0);
const show = x => x && Object.fromEntries(Object.entries(x).map(([k,v]) => [k, Array.isArray(v) ? v.map(String) : typeof v === 'bigint' ? String(v) : v]));
const atStep40Mass = hits.filter(x => x.mass === 293537n);
const allInRootMassGap = hits.every(x => x.mass > 213720n && x.mass < 347700n);
const noStep40State = hits.every(x => x.d !== 239399 || x.a !== 54138n);
console.log(JSON.stringify({
  count: hits.length,
  distinctD: new Set(hits.map(x => x.d)).size,
  min: show(hits[0]),
  max: show(hits[hits.length - 1]),
  atStep40Mass: atStep40Mass.map(show),
  allInRootMassGap,
  noStep40State
}, null, 2));