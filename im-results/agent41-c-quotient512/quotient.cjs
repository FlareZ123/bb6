"use strict";
/** @file Independent parameterized Machine C quotient BFS with explicit representative edges. */
const assert = require("node:assert/strict");
const { performance } = require("node:perf_hooks");
const BASE = 8;
const MOD = Number(process.argv[2] || 64);
assert(Number.isSafeInteger(MOD) && MOD >= 8 && MOD % 8 === 0);
const N = BASE + MOD;
const TOTAL = N ** 3;
assert(Number.isSafeInteger(TOTAL) && TOTAL < 2147483648);
const quotient = x => x < BASE ? x : BASE + (x - BASE) % MOD;
const id = (a,k,c) => (a*N+k)*N+c;
/** @param {number} a @param {number} k @param {number} c @returns {[number,number,number]|null} */
function nextC(a,k,c) {
  if (c===1) return [a,k+1,0];
  if (c===2) return null;
  if (c===3) return [a,k+2,1];
  if (c===0) {
    if (a===0) return [1,0,2*k+2];
    if (a===1) return k===0 ? [5,0,1]:[2,2,2*k-1];
    return [a-2,1,2*k+1];
  }
  if (a===0) return k%2===0 ? [2*k+2,2,c-3] : [2*k+3,0,c];
  return [a-1,k+1,c-1];
}
/** @param {number} i @param {(to:number)=>void} emit */
function successors(i,emit) {
  const c = i%N, k = Math.floor(i/N)%N, a=Math.floor(i/(N*N));
  for (const ra of a < BASE ? [a] : [a,a+MOD])
    for (const rk of k < BASE ? [k] : [k,k+MOD])
      for (const rc of c < BASE ? [c] : [c,c+MOD]) {
        const s=nextC(ra,rk,rc);
        if (s!==null) emit(id(quotient(s[0]),quotient(s[1]),quotient(s[2])));
      }
}
const start=performance.now();
const seen=new Uint8Array(TOTAL),queue=new Int32Array(TOTAL);
let head=0,tail=0,edges=0;
const entry=id(5,0,1);seen[entry]=1;queue[tail++]=entry;
while(head<tail) {
  successors(queue[head++],j=>{edges++;if(!seen[j]){seen[j]=1;queue[tail++]=j;}});
}
const resetExcluded=[]; const sideExcluded=[];
for (let j=0;j<MOD;j++) {
  if (seen[id(quotient(2*(j+MOD)+1),quotient(3*(j+MOD)+4),0)]===0) resetExcluded.push(j);
  if (seen[id(0,quotient(4*(j+MOD)),quotient(24*(j+MOD)+23))]===0) sideExcluded.push(j);
}
const result={base:BASE,modulus:MOD,abstractStates:TOTAL,reachableAbstractStates:tail,examinedAbstractEdges:edges,resetExcludedForAllJGe4ByResidue:resetExcluded,sideExcludedForAllNGe2ByResidue:sideExcluded,
 smallResetExcluded:[1,2,3].filter(j=>seen[id(quotient(2*j+1),quotient(3*j+4),0)]===0),
 smallSideExcluded:[0,1].filter(n=>seen[id(0,quotient(4*n),quotient(24*n+23))]===0),
 elapsedSeconds:(performance.now()-start)/1000};
console.log(JSON.stringify(result,null,2));
