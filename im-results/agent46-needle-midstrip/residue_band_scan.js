#!/usr/bin/env node
// Exact BigInt enumeration of the old and wider residue-cut hypotheses.
// This checks finite range counts only; the all-r arithmetic proof is in
// CancellationMidBandResidue.lean and WIDE-CUT-EXPONENT.md.

function ceilDiv(a, b) { return (a + b - 1n) / b; }

function rangesOf(values) {
  const ranges = [];
  let start = null, previous = null;
  for (const s of values) {
    if (start === null) start = s;
    else if (s !== previous + 1n) {
      ranges.push([start.toString(), previous.toString()]);
      start = s;
    }
    previous = s;
  }
  if (start !== null) ranges.push([start.toString(), previous.toString()]);
  return ranges;
}

function scan(rNumber) {
  const r = BigInt(rNumber);
  const a = (9n ** r + 5n) / 2n;
  const n = 3n ** (2n * r - 1n);
  const d = BigInt(n.toString(2).length); // floor(log2(n)) + 1

  const lowerByCase = ceilDiv(a, 2n * r - 1n);
  const lower = lowerByCase > d ? lowerByCase : d;
  const oldUpper = a / r;
  const oldMiddleUpper = (a - d) / (2n * r - 2n);
  const wideUpper = (2n * a - 2n * d - 1n) / (2n * r - 2n);

  const oldValues = [];
  const wideValues = [];
  let oldNotWide = 0n;

  for (let s = lower; s <= wideUpper; s++) {
    const cut = (a + s - 1n) % s + 1n;
    if (cut < d) continue;

    if (r * s <= a) oldValues.push(s);

    const E = 2n * a - (2n * r - 2n) * s - cut;
    if (E >= d + 1n) wideValues.push(s);
  }

  const wideSet = new Set(wideValues.map(String));
  for (const s of oldValues) if (!wideSet.has(String(s))) oldNotWide++;

  const additional = wideValues.filter(s => r * s > a);
  const beyondOldMiddle = wideValues.filter(s => s > oldMiddleUpper);

  return {
    r: rNumber,
    a: a.toString(),
    d: d.toString(),
    sLower: lower.toString(),
    oldResidueUpper: oldUpper.toString(),
    wideSearchUpper: wideUpper.toString(),
    oldMiddleUpper: oldMiddleUpper.toString(),
    oldResidueCount: oldValues.length.toString(),
    wideResidueCount: wideValues.length.toString(),
    additionalBeyondOldResidueAndMiddle: additional.length.toString(),
    wideValuesBeyondOldMiddleEndpoint: beyondOldMiddle.length.toString(),
    oldSubsetOfWide: oldNotWide === 0n,
    wideRangeCount: rangesOf(wideValues).length,
    wideRanges: rangesOf(wideValues).map(([lo, hi]) => [lo, hi])
  };
}

for (let r = 2; r <= 9; r++) console.log(JSON.stringify(scan(r)));
