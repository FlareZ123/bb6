#!/usr/bin/env node
"use strict";
/*
Discover a rigorous *candidate* one-sided, arbitrary-suffix return:
  (q, U++X, []) ->[k assigned moves] (q, U++V++X, []), or
  (q, [], U++X) ->[k assigned moves] (q, [], U++V++X).
Only the symbolic trial is trusted as a certificate proposal. It operates
with a genuine opaque tail marker, rejects ANY read of that marker, and
requires the exact same unknown tail in the output. The proposed Lean proof
must use Tails.check_sound + a source-checked finite blank seed.
*/
const fs=require("node:fs");
const args=process.argv.slice(2),table=(args[0]||"").replaceAll("_","");
if(table.length!==36)throw Error("usage: node search-one-sided-gliders.cjs SIX_STATE_TABLE [maxSteps=150000] [maxReturn=8000]");
const maxSteps=Number(args[1]||150000),maxReturn=Number(args[2]||8000);
const tr=table.match(/.{3}/g);
for(const t of tr)if(t!=="---"&&!/^[01][LR][ABCDEF]$/.test(t))throw Error("not six-state partial");
function symbolic(q0,prefix,side,delta){
 let q=q0,L=side==="R"?[...prefix,"X"]:[],R=side==="L"?[...prefix,"X"]:[];
 for(let j=0;j<delta;j++){
  const a=L[0]??0;
  if(a==="X")return null;
  const mv=tr[2*q+a];if(mv==="---")return null;
  const w=+mv[0],d=mv[1],next=mv.charCodeAt(2)-65;
  if(d==="R"){
   const b=R[0]??0;if(b==="X")return null;
   L=[b,w,...L.slice(1)];R=R.slice(1);
  }else{L=L.slice(1);R=[w,...R];}
  q=next;
 }
 if(q!==q0)return null;
 const dest=side==="R"?L:R,other=side==="R"?R:L;
 if(other.length!==0||dest.at(-1)!=="X")return null;
 const word=dest.slice(0,-1),width=word.length-prefix.length;
 if(width<=0||width>1000)return null;
 for(let p=0;p<=prefix.length;p++){
  if(word.slice(0,p).every((v,i)=>v===prefix[i]) &&
     word.slice(p+width).every((v,i)=>v===prefix[p+i])){
   return {steps:delta,q:q0,side,prefix:prefix.slice(0,p).join(""),block:word.slice(p,p+width).join(""),prefixLength:p,blockLength:width};
  }
 }
 return null;
}
const tapes=new Set();let q=0,h=0,min=0,max=0,hit=0,records=new Map();
const lens=[16,24,32,48,64,80,96,112,128,160,192,224,256];
function sideBits(side,k){const d=side==="R"?-1:1,base=side==="R"?h:h+1;return Array.from({length:k},(_,i)=>Number(tapes.has(base+d*i)));}
let found=null,attempts=0,skips=0,anchors=0;
for(let n=0;n<maxSteps&&!found;n++){
 let side=null;
 if(h>max){max=h;side="R";}
 else if(h<min){min=h;side="L";}
 // At a fresh R extremum the cells to the right are blank; at a fresh
 // L extremum the current cell is blank, but if a value is already stored
 // to the left of head from a prior far-left excursion, reject.
 if(side){
  anchors++;
  const bits=sideBits(side,256);
  const qb=q,heads=records;
  for(const keylen of [16,32,64,96]){
   const key=side+"/"+q+"/"+bits.slice(0,keylen).join("");
   const prevs=records.get(key)||[];
   for(let j=prevs.length-1;j>=0;j--){
    const x=prevs[j],dt=n-x.n,dh=(side==="R"?h-x.h:x.h-h);
    if(dt<=0||dt>maxReturn||dh<=0)continue;
    for(const len of lens){
     if(len>256)continue;
     const src=x.bits.slice(0,len);
     const test=symbolic(q,src,side,dt);
     attempts++;
     if(test&&test.blockLength===dh){
      found={table:table.match(/.../g).join("_"),source_step:x.n,target_step:n,source_head:x.h,target_head:h,
        ...test,seed_side:side,notes:"Certificate candidate: source-check the symbolic return and finite seed independently."};
      break;
     }
    }
    if(found)break;
   }
   if(found)break;
   const next=prevs.filter(x=>n-x.n<=maxReturn);
   next.push({n,h,bits});if(next.length>7)next.shift();
   records.set(key,next);
  }
 }
 const m=tr[2*q+Number(tapes.has(h))];if(m==="---"){hit=n;break;}
 if(+m[0])tapes.add(h);else tapes.delete(h);
 h+=m[1]==="R"?1:-1;q=m.charCodeAt(2)-65;
}
const out={found,stats:{stepsScanned:found?found.target_step:maxSteps,anchors,attempts,recordKeys:records.size,table,wasUnknownRead:hit>0}};
process.stdout.write(JSON.stringify(out,null,2)+"\n");
