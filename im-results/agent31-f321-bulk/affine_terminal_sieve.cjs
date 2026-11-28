#!/usr/bin/env node
"use strict";
/*
  SOURCE-FAITHFUL FINITE PROOF-SEARCH / CERTIFICATE CONSTRUCTOR FOR F321.
  Input: a residue class of possible halting parameters d ≡ r (mod M).
  A symbolic state [p,a,q,b] denotes (p*n+a, q*n+b), ALL n>=0.
  The enumerated one-step inverse branches are EXACTLY those of the
  DeepMind c86f158 F321 two-counter map. Branches not universally decidable
  at the current modulus return UNKNOWN, never a false exclusion.
  If all finite inverse branches reach predecessor-free states and no
  state contains (1,1), the entire infinite congruence class is excluded.

  This program is a reproducible computational certificate, NOT a Lean
  kernel theorem or a whole F321 nonhalting proof.
*/
const assert=require("node:assert/strict");
const {createHash}=require("node:crypto");

function rootPossible(p,a,q,b) {
  if(a>1||b>1)return false;
  if(p===0&&a!==1 || q===0&&b!==1)return false;
  let n=null;
  if(p!==0){
    if((1-a)%p!==0)return false;
    n=(1-a)/p;
  }
  if(q!==0){
    if((1-b)%q!==0)return false;
    const m=(1-b)/q;
    if(n!==null&&n!==m)return false;
    n=m;
  }
  return n===null||n>=0;
}

function classify(r,M,maxNodes=1000) {
  assert(Number.isSafeInteger(M)&&M>=1&&M<=2**23);
  assert(Number.isSafeInteger(r)&&r>=0&&r<M);
  const work=[[M,r+1,M,r]], seen=new Set();
  let expanded=0;
  while(work.length){
    if(expanded++>=maxNodes)return {excluded:false,why:"node-limit",expanded};
    const [p,a,q,b]=work.pop(),key=[p,a,q,b].join(",");
    if(seen.has(key))continue;
    seen.add(key);
    // For every accepted inverse, p+q=2M remains invariant; a+b
    // decreases by at least one. All arithmetic is exact safe integers
    // for M<=2^23, because initial a+b<=2M and never increases.
    assert(p>=0&&q>=0&&a>=0&&b>=0&&p+q===2*M);
    assert(a+b<=2*M);
    if(rootPossible(p,a,q,b))return{excluded:false,why:"contains-seed",expanded};
    // Unknown high parity or exceptional D=1: must NOT claim closure.
    if(q%2!==0)return {excluded:false,why:"high-parity",expanded};
    if(b%2!==0 && b<3)return{excluded:false,why:"high-threshold",expanded};
    if(q>0 && b<=1)return{excluded:false,why:"equality-exception",expanded};
    if(p%4!==0)return{excluded:false,why:"far-parity",expanded};

    if(b%2===1){
      // D>=3 odd uniformly, exact unique high inverse
      work.push([p+q/2,a+(b-3)/2+2,q/2,(b-3)/2]);
    }
    if(q===0&&b===1){
      if(p%2!==0)return{excluded:false,why:"equality-parity",expanded};
      if(a%2===0&&a>=4)
        work.push([p/2,(a-4)/2,p/2,(a-4)/2]);
      else if(p>0)return{excluded:false,why:"equality-threshold",expanded};
    }
    if(a%4===2){
      if(a<6||b<1)return{excluded:false,why:"far-threshold",expanded};
      const x=p/4,y=(a-6)/4;
      work.push([x,y,q+3*x,b+3*y]);
    }
    // Middle inverse has potentially O(n) solutions, so do NOT branch
    // symbolically without a separate lemma. Return UNKNOWN instead.
    if((q===0&&(b===1||b===2))||(q>0&&b<=2)){
      if(a%4===2&&(a>=10||p>0))
        return{excluded:false,why:"middle-branch",expanded};
    }
  }
  return {excluded:true,expanded};
}

function report(bits=20, maxNodes=1000){
  assert(Number.isSafeInteger(bits)&&bits>=1&&bits<=23);
  const M=2**bits, mask=Buffer.alloc(M/8+1);
  let accepted=0,uncertain={},maxExpanded=0,totalExpanded=0;
  for(let r=0;r<M;r++){
    const v=classify(r,M,maxNodes);
    totalExpanded+=v.expanded;
    maxExpanded=Math.max(maxExpanded,v.expanded);
    if(v.excluded){accepted++;mask[r>>3]|=1<<(r&7);}
    else uncertain[v.why]=(uncertain[v.why]||0)+1;
  }
  return {bits,modulus:M,excludedResidues:accepted,uncertifiedResidues:M-accepted,
    certifiedDensity:accepted/M,certificateBitsetSHA256:createHash("sha256")
      .update(mask.subarray(0,Math.ceil(M/8))).digest("hex"),
    maxExpanded,totalExpanded,uncertain};
}
if(require.main===module){
  const bits=Number(process.argv[2]||20);
  const outcome=report(bits);
  if(bits===20)assert.equal(outcome.excludedResidues,1038925);
  process.stdout.write(JSON.stringify(outcome,null,2)+"\n");
}
module.exports={rootPossible,classify,report};
