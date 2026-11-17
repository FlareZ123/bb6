#!/usr/bin/env node
// Exact enumeration of the residue-cut hypotheses (R) in RESIDUE-CUT-EXTENSION.md.
// This checks range counts only; the all-r proof is the accompanying paper argument.

function ceilDiv(a, b) { return (a + b - 1n) / b; }

function scan(rNumber) {
  const r = BigInt(rNumber);
  const a = (9n ** r + 5n) / 2n;
  const n = 3n ** (2n * r - 1n);
  const d = BigInt(n.toString(2).length); // floor(log2(n)) + 1

  const lowerByCase = ceilDiv(a, 2n * r - 1n);
  const lower = lowerByCase > d ? lowerByCase : d;
  const upper = a / r;
  const oldUpper = (a - d) / (2n * r - 2n);

  const ranges = [];
  let start = null, previous = null;
  let count = 0n, extensionCount = 0n;

  for (let s = lower; s <= upper; s++) {
    const cut = (a + s - 1n) % s + 1n;
    if (cut >= d) {
      count++;
      if (s > oldUpper) extensionCount++;
      if (start === null) start = s;
      previous = s;
    } else if (start !== null) {
      ranges.push([start.toString(), previous.toString()]);
      start = null;
      previous = null;
    }
  }
  if (start !== null) ranges.push([start.toString(), previous.toString()]);

  return {
    r: rNumber, a: a.toString(), d: d.toString(),
    sLower: lower.toString(), sUpper: upper.toString(),
    oldUpper: oldUpper.toString(),
    qualifyingCount: count.toString(),
    newBeyondOldCount: extensionCount.toString(),
    ranges
  };
}

for (let r = 2; r <= 9; r++) console.log(JSON.stringify(scan(r)));
