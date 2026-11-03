"use strict";

const assert = require("node:assert/strict");
const RLE = "1RB---_1LC1LF_1LD0LC_0LE1RF_1RA1LA_1LB0RD";
const table = RLE.split("_").map((pair) => [pair.slice(0, 3), pair.slice(3)].map((token) => {
  if (token === "---") return null;
  assert.match(token, /^[01][LR][A-F]$/);
  return {write: Number(token[0]), shift: token[1] === "R" ? 1 : -1, next: token.charCodeAt(2) - 65};
}));
assert.equal(table.length, 6);

/** @typedef {{rawStep:number,head:number,signature:number}} Candidate */
/** @param {number} maxSteps Number of successful raw transitions to test. */
function test(maxSteps) {
  const offset = 2_000_000;
  const tape = new Uint8Array(2 * offset + 1);
  let q = 0;
  let h = offset;
  let totalB = 0;
  const rCounts = new Map();
  const signatureCounts = new Map();
  /** @type {Candidate | null} */
  let firstR2 = null;
  for (let step = 0; step < maxSteps; step++) {
    const bit = tape[h];
    const rule = table[q][bit];
    assert.ok(rule, "Unexpected auxiliary halt at step " + step);
    if (q === 1 && bit === 0) {
      totalB++;
      let r = 0;
      while (tape[h - r - 1] === 1) {
        r++;
        assert.ok(h - r - 4 >= 0, "Bound exceeded during left scan at " + step);
      }
      let signature = 0;
      for (let k = 1; k <= 4; k++) signature = 2 * signature + tape[h - r - k];
      const key = r + ":" + signature.toString(2).padStart(4, "0");
      rCounts.set(r, (rCounts.get(r) ?? 0) + 1);
      signatureCounts.set(key, (signatureCounts.get(key) ?? 0) + 1);
      if (r === 2 && firstR2 === null) firstR2 = {rawStep: step, head: h - offset, signature};
      assert.notEqual(signature, 3, "Forbidden 0011 boundary at B/0, raw step " + step);
    }
    tape[h] = rule.write;
    h += rule.shift;
    q = rule.next;
    assert.ok(h > 100 && h < tape.length - 100, "Head out of buffer on step " + step);
  }
  assert.equal(totalB, Array.from(rCounts.values()).reduce((a,b)=>a+b, 0));
  const distribution = [...rCounts].sort(([a],[b])=>a-b);
  const signatures = [...signatureCounts].sort(([a],[b])=>a.localeCompare(b));
  console.log(JSON.stringify({machine:RLE, rawSteps:maxSteps, B0Sections:totalB, firstR2, distribution, signatures, finalState:"ABCDEF"[q],finalHead:h-offset}, null, 2));
  return {totalB, distribution, signatures, firstR2};
}
const output=test(50_000_000);
assert.equal(output.totalB, 70409);
assert.deepEqual(output.distribution, [[0,558],[1,22583],[2,9],[3,47226],[4,33]]);
assert.deepEqual(output.firstR2, {rawStep:3194871,head:-693,signature:5});
console.log("PASS: raw 50-million-step typed-array replay and independent C++ count agreement");
console.log("Finite experiment, no all-time blank-root theorem.");
