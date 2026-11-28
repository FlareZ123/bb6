#!/usr/bin/env node
"use strict";

/* Verifies the 136 small-K instances of the sharp signed valuation packing
   inequality, and reports the three exceptional lower K. The proof for
   K>=151 is algebraic; see results/2026-11-28-sharp-signed-valuation-packing-agent22.md.
*/
function F(n) {
  if (!Number.isSafeInteger(n) || n<0) throw new Error("F expects nonnegative integer");
  let total=0;
  while (n) {total+=n; n=Math.floor(n/4);}
  return total;
}
function U(K) {
  if (!Number.isSafeInteger(K) || K<=0) throw new Error("K must be positive");
  return F(Math.floor((K-1)/3))-F(Math.floor(K/4));
}
let maxima=-Infinity, equality=[], checked=0;
for (let K=15; K<=150; K++) {
  const discrepancy=15*U(K)-2*K;
  if (discrepancy>0) throw new Error("Counterexample K="+K);
  if (discrepancy===0) equality.push(K);
  maxima=Math.max(maxima,discrepancy);
  checked++;
}
if (checked!==136 || maxima!==0 || String(equality)!=="15")
  throw new Error("Unexpected small-range profile");
const exceptions=[];
for(let K=1;K<15;K++)if(15*U(K)>2*K)exceptions.push(K);
if(String(exceptions)!=="7,13,14")throw new Error("Unexpected small exception list");
console.log(JSON.stringify({checked,Kmin:15,Kmax:150,maximumDiscrepancy:maxima,
  equality,exceptionsBelow15:exceptions,sharpWitness:{K:15,v:1,j:2,next:1}}));
module.exports={F,U};
