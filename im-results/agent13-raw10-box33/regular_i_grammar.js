#!/usr/bin/env node
"use strict";
// Raw10 I REGULAR-INVARIANT CANDIDATE: primitive-verified finite tests only.
// Semantic target: H_j(U)=F_(j+2)(F_j(U)), j grows by FOUR per update.
const C=[8,24,11,18,1,13,17,3,12,0,4,21];
const D={Z:"0000",P:"0010",Q:"0100",R:"0101",S:"1000",T:"1010",U:"1100"};
const bits=ds=>ds.map(x=>D[x]).join("");
const trim=s=>s.replace(/0+$/,"");
function* N(k) {
  if(k<1)return;
  yield ["T"];
  if(k>=2)yield ["Q","Q"];
  for(const b of B(k-1)){yield ["S",...b];yield ["R",...b];}
}
function* B(k) {
  if(k<0)return;
  yield [];
  if(k>=1){yield ["P"];yield ["Q"];yield ["U"];}
  for(const n of N(k-1)){yield ["Z",...n];yield ["P",...n];}
}
// N ::= S B | R B | T | Q Q
// B ::= epsilon | P | Q | U | Z N | P N
function nextN(n){
 const [x,...r]=n;
 if(x==="S")return ["R",...r];
 if(x==="R")return ["S",...nextB(r)];
 if(n.length===1&&x==="T")return ["Q","Q"];
 if(n.length===2&&x==="Q"&&n[1]==="Q")return ["S","U"];
 throw Error("Invalid N: "+n.join("/"));
}
function nextB(b){
 if(!b.length)return ["P"];
 if(b.length===1){
  if(b[0]==="P")return ["Z","T"];
  if(b[0]==="Q")return ["Z","S"];
  if(b[0]==="U")return ["Q"];
 }
 if(b[0]==="Z")return ["P",...b.slice(1)];
 if(b[0]==="P")return ["Z",...nextN(b.slice(1))];
 throw Error("Invalid B: "+b.join("/"));
}
const p=j=>"01010010"+"0010".repeat(j);
function atBoundary(tape,q,h,j,s){
 if(q!==0)return false;
 const v=p(j)+s;
 for(const i of tape)if(i<h||i>=h+v.length)return false;
 for(let i=0;i<v.length;i++)if((tape.has(h+i)?"1":"0")!==v[i])return false;
 return true;
}
function rawStep(tape,q,h){
 const v=C[2*q+(tape.has(h)?1:0)]-1;
 if(v<0)return null;
 if((v>>1)&1)tape.add(h);else tape.delete(h);
 return [v>>2,h+((v&1)?1:-1)];
}
function blankAt(n,j,s){
 const tape=new Set();let q=0,h=0;
 for(let t=0;t<n;t++){
  const v=rawStep(tape,q,h);
  if(v===null)throw Error("Unexpected blank halt at "+t);
  [q,h]=v;
 }
 return atBoundary(tape,q,h,j,s);
}
function F(word,j,limit=10000){
 const initial=p(j)+"10101"+word,target=p(j+2)+"10101";
 const tape=new Set([...initial].flatMap((c,i)=>c==="1"?[i]:[]));
 let q=0,h=0;
 for(let t=0;t<limit;t++){
  if(t>0&&q===0){
   let leftBlank=true;
   for(const i of tape)if(i<h){leftBlank=false;break;}
   if(leftBlank){
    let okay=true;
    for(let i=0;i<target.length;i++)
     if((tape.has(h+i)?"1":"0")!==target[i]){okay=false;break;}
    if(okay){
     const start=h+target.length,stop=Math.max(start,...tape);
     const rest=Array.from({length:Math.max(0,stop-start+1)},(_,i)=>
       tape.has(start+i)?"1":"0").join("");
     return {kind:"return",rest,steps:t};
    }
   }
  }
  const v=rawStep(tape,q,h);
  if(v===null)return {kind:"halt",steps:t};
  [q,h]=v;
 }
 return {kind:"timeout",limit};
}
function verify(maxTokens=12){
 if(!blankAt(490,3,"1010111")||!blankAt(1500,7,"1010100001"))
   throw Error("Incorrect blank entry boundary");
 let tested=0,maxBits=0,maxSteps=0;
 for(const n of N(maxTokens-1)){
  if(n[0]!=="S"&&n[0]!=="R")continue;
  const input=trim(bits(["Z",...n])),expected=trim(bits(["Z",...nextN(n)]));
  const x=F(input,3);
  if(x.kind!=="return")throw Error(JSON.stringify({input,x}));
  const y=F(x.rest,5);
  if(y.kind!=="return"||y.rest!==expected)
   throw Error(JSON.stringify({input,expected,x,y}));
  tested++;maxBits=Math.max(maxBits,input.length);
  maxSteps=Math.max(maxSteps,x.steps+y.steps);
 }
 return {source:C,maxTokens,tested,maxBits,maxSteps,
   exactBlank490:true,exactBlank1500:true,failures:0,
   machineUniversalProof:false};
}
if(require.main===module){
 const k=Number(process.argv[2]||12);
 if(!Number.isInteger(k)||k<2||k>24)throw Error("2<=maxTokens<=24 required");
 console.log(JSON.stringify(verify(k),null,2));
}
module.exports={D,N,B,nextN,nextB,F,blankAt,verify};
