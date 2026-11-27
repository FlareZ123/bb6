#!/usr/bin/env node
"use strict";

/* Deterministic tests of the proposed complete two-phase regular zipper
   invariant. These tests are not a proof; the proof is in the accompanying
   paper-level derivation and needs a Lean source-connected port. */

const literal="1RB0LA_1RC0LE_0RD1RF_1LD0RB_1LA1RA_0RE---";
const tr=literal.split("_").map(row => [row.slice(0,3),row.slice(3,6)].map(s =>
  s==="---" ? null : [+s[0],s[1]==="R" ? 1 : -1,s.charCodeAt(2)-65]));
const one=(n)=>"1".repeat(n), zero=(n)=>"0".repeat(n);

let rng=0x9e3779b9;
function rand(k){
  rng ^= rng<<13; rng ^= rng>>>17; rng ^= rng<<5;
  return (rng>>>0)%k;
}
function inner(){
  let n=rand(4),v="";
  for(let j=0;j<n;j++)v+="0"+one(5*(1+rand(4))+1);
  return v;
}
function O(){
  return rand(2) ? one(5*(1+rand(4))) :
      one(5*rand(4)+3)+inner()+"0"+one(5*rand(4)+3);
}
function A(){return one(5*rand(4)+3)+inner();}
function B(){
  return rand(2) ? one(5*rand(4)+2) :
      one(5*rand(4)+3)+inner()+"0"+one(5*(1+rand(4)));
}
const O0="1{5}(?:1{5})*", O3="1{3}(?:1{5})*",
  O2="1{2}(?:1{5})*", O1="1{6}(?:1{5})*";
const outer="(?:"+O0+"|"+O3+"(?:0"+O1+")*0"+O3+")";
const al=O3+"(?:0"+O1+")*";
const bl="(?:"+O2+"|"+O3+"(?:0"+O1+")*0"+O0+")";
const leftA=new RegExp("^(?:"+outer+"00)*"+al+"$");
const leftB=new RegExp("^(?:"+outer+"00)*"+bl+"$");
const WB="(?:0{2}|0{4})(?:0{5})*101";
const rightA=new RegExp("^01(?:0(?:0{5})*101(?:"+WB+")*)?$");
const rightB=new RegExp("^(?:"+WB+")*$");
const W=()=>zero(5*rand(4)+(rand(2)?2:4))+"101";
function makeLeft(phase){
  let outerFrames=Array.from({length:rand(5)},O);
  return [...outerFrames,phase==="A"?A():B()].join("00");
}
function makeRight(which){
  const rest=Array.from({length:rand(4)},W).join("");
  switch(which){
    case "Aonly":return "01";
    case "Ashort":return "010101"+rest;
    case "Along":return "01"+zero(5*(1+rand(4))+1)+"101"+rest;
    case "Bempty":return "";
    case "B2short":return "00101"+rest;
    case "B4short":return "0000101"+rest;
    case "B2long":return zero(5*(1+rand(4))+2)+"101"+rest;
    case "B4long":return zero(5*(1+rand(4))+4)+"101"+rest;
  }
  throw new Error("bad branch");
}
const cases=["Aonly","Ashort","Along","Bempty","B2short","B4short","B2long","B4long"];
const counts=Object.fromEntries(cases.map(x=>[x,0]));
function check(which){
  const phase=which[0]==="A"?"A":"B";
  const L=makeLeft(phase),R=makeRight(which),isA=phase==="A";
  if(!(isA?leftA:leftB).test(L)||!(isA?rightA:rightB).test(R))
    throw new Error("invalid generator: "+JSON.stringify({which,L,R}));
  const tape=new Set();
  for(let i=0;i<L.length;i++)if(L[i]==="1")tape.add(i-L.length);
  for(let i=0;i<R.length;i++)if(R[i]==="1")tape.add(i);
  let q=5,h=0,t=0,readF1=false;
  const maxSteps=10000;
  do{
    const a=+tape.has(h);
    if(q===5&&a===1)readF1=true;
    const mv=tr[q][a];
    if(!mv)throw new Error("queried missing row: "+JSON.stringify({which,L,R,h,t,q}));
    if(mv[0])tape.add(h);else tape.delete(h);
    h+=mv[1];q=mv[2];t++;
    if(t>maxSteps)throw new Error("did not reach F within "+maxSteps+" steps");
  }while(q!==5);
  let left="",right="",min=Math.min(...[...tape].filter(x=>x<h)),
    max=Math.max(h-1,...[...tape].filter(x=>x>=h));
  for(let i=min;i<h;i++)left+=tape.has(i)?"1":"0";
  for(let i=h;i<=max;i++)right+=tape.has(i)?"1":"0";
  const nextPhase=(phase==="A"||which==="Bempty"||which.endsWith("long"))?
      (phase==="A"?"B":"A"):"B";
  const accepted=nextPhase==="A"?(leftA.test(left)&&rightA.test(right)):
      (leftB.test(left)&&rightB.test(right));
  if(!accepted||readF1||tape.has(h))
    throw new Error("invariant not preserved: "+JSON.stringify({
      which,L,R,t,h,left,right,nextPhase,accepted,readF1}));
  const fixedCosts={Aonly:18,Ashort:8,Along:18,B2short:11,B4short:11};
  if(fixedCosts[which]!==undefined&&t!==fixedCosts[which])
    throw new Error("incorrect short-macro cost");
  if(phase==="B"&&fixedCosts[which]===undefined){
    const terminal=L.split("00").at(-1);
    const lengths=terminal.split("0").map(s=>s.length),sum=lengths.reduce((a,b)=>a+b,0);
    if(t!==sum+18+9*lengths.length || h!==2-sum-lengths.length)
      throw new Error("incorrect carry cost/displacement: "+JSON.stringify({
        which,lengths,t,h}));
  }
  counts[which]++;
}
for(let i=0;i<32000;i++)check(cases[i%cases.length]);
console.log(JSON.stringify({status:"regular invariant sampled sections passed",
  machine:literal,counts,formalProof:false}));
