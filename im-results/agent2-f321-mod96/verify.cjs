#!/usr/bin/env node
'use strict';
// Sound nondeterministic modulo-96 overapproximation of the exact F321
// source counter map AFTER its authentic first move (1,1)->(6,1).
// Both middle outputs are allowed unconditionally, high/far are allowed
// unconditionally, equality only when the two residues agree.
// This is therefore a SUPerset of all authentic post-seed residues.
const N=96, mod=x=>(x%N+N)%N, idx=(a,d)=>a*N+d;
const seen=new Uint8Array(N*N), q=[[6,1]]; seen[idx(6,1)]=1;
const succ=(a,d)=>{
  const x=mod(4*a+6);
  const s=[[mod(a-d-2),mod(2*d+3)],[x,mod(d-3*a)],[x,1],[x,2]];
  if(a===d)s.push([mod(2*a+4),1]);
  return s;
};
for(let i=0;i<q.length;i++)
  for(const [a,d] of succ(...q[i])) {
    const z=idx(a,d);
    if(!seen[z]){seen[z]=1;q.push([a,d]);}
  }
let mask=0n;
for(let i=0;i<seen.length;i++)if(seen[i])mask|=(1n<<BigInt(i));
for(const [a,d] of q)for(const [A,D] of succ(a,d))
  if(!seen[idx(A,D)])throw Error('not inductive');
const gates=[];
for(let d=0;d<N;d++)if(seen[idx((d+1)%N,d)])gates.push(d);
if(gates.includes(13)||gates.length!==6||q.length!==811)
  throw Error('incompatible modulo quotient');
const output={sourceSeed:[1,1],entry:[6,1],modulus:N,reachableQuotientStates:q.length,
  possibleGateResidues:gates,excludedNewFullProgression:'d=13+96u, u>=0',
  overapproxDescription:'unconditional H,F,M1,M2; equality only for x=y',
  compressedSourceMaskHexDigits:mask.toString(16).length,certMaskHex:'0x'+mask.toString(16)};
console.log(JSON.stringify(output,null,2));
