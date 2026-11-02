"use strict";

/** Sound finite-state overapproximation of the BB(6) Machine C counter map.
 * The code runs exact integer arithmetic on bounded abstract representatives.
 * This is an intermediate certificate, not a Machine C halting decision.
 */
const assert = require("node:assert/strict");
const BASE=8, MOD=64, N=BASE+MOD, TOTAL=N**3;

/** @param {number} x @returns {number} */
function quotient(x) { return x<BASE?x:BASE+(x-BASE)%MOD; }
/** @param {number} x @returns {number[]} */
function reps(x) { return x<BASE?[x]:[x,x+MOD]; }

/** @param {number} a @param {number} k @param {number} c
 * @returns {[number,number,number]|null} */
function nextC(a,k,c) {
  if(c===1) return [a,k+1,0];
  if(c===2) return null;
  if(c===3) return [a,k+2,1];
  if(c===0) {
    if(a===0) return [1,0,2*k+2];
    if(a===1) return k===0?[5,0,1]:[2,2,2*k-1];
    return [a-2,1,2*k+1];
  }
  if(a===0) return k%2===0?[2*k+2,2,c-3]:[2*k+3,0,c];
  return [a-1,k+1,c-1];
}

/** @param {number} a @param {number} k @param {number} c */
function index(a,k,c) { return (a*N+k)*N+c; }
/** @param {number} i @returns {[number,number,number]} */
function unpack(i) {
  const c=i%N, k=Math.floor(i/N)%N, a=Math.floor(i/(N*N));
  return [a,k,c];
}
/** @param {number} i @param {(j:number)=>void} emit */
function successors(i,emit) {
  const [a,k,c]=unpack(i);
  for(const ra of reps(a)) for(const rk of reps(k)) for(const rc of reps(c)) {
    const t=nextC(ra,rk,rc);
    if(t!==null) emit(index(quotient(t[0]),quotient(t[1]),quotient(t[2])));
  }
}
/** @returns {{seen:Uint8Array,count:number,edges:number}} */
function closure() {
  const seen=new Uint8Array(TOTAL), queue=new Int32Array(TOTAL);
  let head=0,tail=0,edges=0;
  seen[index(5,0,1)]=1; queue[tail++]=index(5,0,1);
  while(head<tail) successors(queue[head++],j=>{
    edges++;
    if(!seen[j]) { seen[j]=1;queue[tail++]=j; }
  });
  return {seen,count:tail,edges};
}
/** @param {Uint8Array} seen */
function verifyClosure(seen) {
  assert.equal(seen[index(5,0,1)],1);
  for(let i=0;i<TOTAL;i++) if(seen[i]) {
    successors(i,j=>assert.equal(seen[j],1,`Open edge ${i} -> ${j}`));
  }
}
/** @param {Uint8Array} seen @param {number} j */
function hasReset(seen,j) {
  return seen[index(quotient(2*j+1),quotient(3*j+4),0)]===1;
}
/** @param {Uint8Array} seen @param {number} n */
function hasSide(seen,n) {
  return seen[index(0,quotient(4*n),quotient(24*n+23))]===1;
}
/** @returns {object} */
function main() {
  const {seen,count,edges}=closure();
  verifyClosure(seen);
  const resetExcluded=Array.from({length:MOD},(_,r)=>r)
    .filter(r=>!hasReset(seen,r+MOD));
  const sideExcluded=Array.from({length:MOD},(_,r)=>r)
    .filter(r=>!hasSide(seen,r+MOD));
  const smallResetExcluded=[1,2,3].filter(j=>!hasReset(seen,j));
  const smallSideExcluded=[0,1].filter(n=>!hasSide(seen,n));
  assert.deepEqual([3,7,16,19,22,58,59].filter(j=>!resetExcluded.includes(j)),[]);
  assert.deepEqual([0,16,32,48].filter(n=>!sideExcluded.includes(n)),[]);
  return {base:BASE,modulus:MOD,abstractStates:TOTAL,
    reachableAbstractStates:count,examinedAbstractEdges:edges,
    resetExcludedForAllJGe4ByResidue:resetExcluded,smallResetExcluded,
    sideExcludedForAllNGe2ByResidue:sideExcluded,smallSideExcluded};
}
if(require.main===module) console.log(JSON.stringify(main(),null,2));
module.exports={quotient,reps,nextC,successors,closure,verifyClosure,hasReset,hasSide,main};
