"use strict";

/**
 * Exact affine certificate for a P1 forbidden critical-index family.
 * [A,B,C] represents A*w+B*v+C with natural v and w >= v+1.
 * This program checks exact integer identities and strict inequalities.
 * It is computational evidence, pending a Lean kernel proof.
 */
const mk=(a,b,c)=>[BigInt(a),BigInt(b),BigInt(c)];
/** @param {bigint[]} a @param {bigint[]} b @returns {bigint[]} */
const add=(a,b)=>a.map((x,i)=>x+b[i]);
/** @param {bigint[]} a @param {bigint} k @returns {bigint[]} */
const times=(a,k)=>a.map(x=>x*k);
/** @param {bigint[]} a @param {bigint} k @returns {bigint[]} */
const divideExact=(a,k)=>{
  if(!a.every(x=>x%k===0n))throw Error(`Nonintegral polynomial: ${a} / ${k}`);
  return a.map(x=>x/k);
};
/** @param {bigint[]} a @param {bigint} m @returns {bigint} */
const commonMod=(a,m)=>{
  if(a[0]%m||a[1]%m)throw Error(`Nonconstant residue: ${a} modulo ${m}`);
  return ((a[2]%m)+m)%m;
};
/** The substitution w=(v+1)+u reduces the inequality to coefficients.
 * @param {bigint[]} a @param {bigint} minimum
 */
const proveLower=(a,minimum)=>{
  if(a[0]<0n||a[0]+a[1]<0n||a[0]+a[2]<minimum)
    throw Error(`Failed universal lower bound ${a} >= ${minimum}`);
};
const C=n=>mk(0,0,n);
const rootB=mk(229376,-2048,-44);
const rootD=C(3);
const X=mk(16384,0,0);
const nodes=[];
const leaves=[];
const encode=a=>a.map(String);
/** @param {bigint[]} b @param {bigint[]} d @param {number[]} path */
function visit(b,d,path){
  if(path.length>24||nodes.length>200)throw Error("Unclosed inverse tree");
  proveLower(b,8n); proveLower(d,1n);
  if(commonMod(b,4n)!==0n)throw Error("G output must be divisible by four");
  nodes.push({path,b:encode(b),d:encode(d)});
  let k=add(divideExact(b,4n),C(-1));
  let z=add(d,divideExact(b,2n));
  proveLower(k,2n);
  let index=0;
  while(true){
    proveLower(z,2n); // Excludes exceptional G input 1.
    const x=add(times(k,2n),C(-4));
    const y=add(z,C(4));
    proveLower(x,8n); proveLower(y,1n);
    const edge=path.concat(index);
    if(commonMod(y,2n)===0n){
      const potentialPower=add(x,C(12));
      // Reachable even-positive hub requires x+12=14*2^j.
      // Here 7*X < x+12 < 14*X, X=2^(1024*v+14).
      proveLower(add(potentialPower,times(X,-7n)),1n);
      proveLower(add(times(X,14n),times(potentialPower,-1n)),1n);
      leaves.push({path:edge,kind:"power-gap",value:encode(potentialPower)});
    }else{
      const r=commonMod(x,4n);
      if(r===2n){
        proveLower(x,3n);
        leaves.push({path:edge,kind:"mod4",value:encode(x)});
      }else if(r===0n)visit(x,y,edge);
      else throw Error(`Unexpected residue at ${edge}`);
    }
    if(commonMod(z,2n)===0n)break;
    const next=divideExact(add(z,C(-3)),2n);
    proveLower(next,2n);
    const q=commonMod(next,2n);
    k=add(add(k,divideExact(add(next,C(-q)),2n)),C(1));
    z=next;
    if(++index>20)throw Error("Infinite G inverse nesting");
  }
}
visit(rootB,rootD,[]);
if(nodes.length!==15||leaves.length!==30)throw Error("Unexpected certificate size");
console.log(JSON.stringify({
  hypothesis:"v>=0, w>=v+1",
  target:"Unreachable P1 hub (229376*w-2048*v-44,3) when w=2^(1024*v)",
  nodes:nodes.length,leaves:leaves.length,
  powerGapLeaves:leaves.filter(x=>x.kind==="power-gap").length,
  mod4Leaves:leaves.filter(x=>x.kind==="mod4").length,
  proofTree:{nodes,leaves}
},null,2));
