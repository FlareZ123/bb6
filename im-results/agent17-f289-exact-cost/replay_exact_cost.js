// Exact-cost candidate replay using Agent42's checkpoint-matched state engine.
// Usage: node replay_exact_cost.js /path/to/pinned/F289-machine.lean
// Arithmetic is kernel-checked in RleCostAlgebra.lean; source semantics remain separate proof obligations.
'use strict';
const fs = require('node:fs');
const path = require('node:path');
const original = path.join(__dirname, '../agent42-cryptids-upstream-191-overlap/simulate_f289_rle.js');
const replacements = {
  "const segWeight = segs => segs.reduce((a,[r,c])=>a+c*(6n*r+30n),0n);": "const segWeight = segs => segs.reduce((a,[r,c])=>a+c*(6n*r+26n),0n);",
  "const cleanDR0Zeros = (q,c0,bot,S) => 6n*q*(c0+bot)+15n*q*q+41n*q+q*S;": "const cleanDR0Zeros = (q,c0,bot,S) => 6n*q*(c0+bot)+15n*q*q+35n*q+q*S;",
  "const cleanRNILOne = (c0,bot,S) => 6n*c0+6n*bot+61n+S;": "const cleanRNILOne = (c0,bot,S) => 6n*c0+6n*bot+57n+S;",
  "const cleanRNILZeroPow = (q,bot,S) => 6n*q*bot+18n*q*q+49n*q+q*S;": "const cleanRNILZeroPow = (q,bot,S) => 6n*q*bot+16n*q*q+41n*q+q*S;",
  "const cleanP1Pow = (q,r,bot,S) => q*(10n*r+6n*bot+6n*q+75n+S)+(6n*r+42n)*q*(q-1n)/2n;": "const cleanP1Pow = (q,r,bot,S) => q*(7n*r+50n+6n*bot+S)+(3n*r+25n)*q*q;",
  "const cleanP2Pow = (q,r,bot,S) => q*(15n*r*r+113n*r+165n)+(6n*r+12n)*(q*bot+(r+1n)*q*(q+1n)/2n)+(r+2n)*(q*S+(24n*r+48n)*q*(q-1n)/2n);": "const cleanP2Pow = (q,r,bot,S) => q*(37n*r+48n+6n*bot*(r+1n)+(r+1n)*S)+(r+1n)*(15n*r+25n)*q*q;",
  "items[1].c*(4n*items[1].r+15n)": "items[1].c*(4n*items[1].r+11n)",
  "4n*(items[0].c-3n)+15n": "4n*(items[0].c-3n)+11n",
  "S+6n*(c0-1n)+30n": "S+6n*(c0-1n)+26n",
  "if(machineRLE===allowedRLEs[0])\n  assert.equal(total,1003448704258405241756955830449585121679083838719n,'first F289 cost bound changed');": "",
  "primitiveStepUpperBound:String(primitiveStepUpperBound),": "successfulPrimitiveStepCandidate:String(primitiveStepUpperBound),\n  includingHaltAttemptCandidate:String(primitiveStepUpperBound+1n),",
  "rleTransitionCostUpperBound:String(total),": "rleTransitionCostCandidate:String(total),"
};
let code = fs.readFileSync(original, 'utf8');
for (const [oldText, newText] of Object.entries(replacements)) {
  if (!code.includes(oldText)) throw new Error('Original engine changed: ' + oldText);
  code = code.split(oldText).join(newText);
}
new Function('require', 'process', 'console', code)(require, process, console);
