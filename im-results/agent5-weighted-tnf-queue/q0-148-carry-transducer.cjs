#!/usr/bin/env node
"use strict";
/**
 * Exact-source test of the q0-148 3-carry symbolic boundary transducer.
 * The theorem candidates are in Q0148BoundarySweep.lean.
 * This is a bounded regression test, NOT a BB(6) source Cover.
 */
const raw="1RB1LC1RC0RE0LA0LD1LA0RF1RB1RD0RC---";
const T=Array.from({length:12},(_,i)=>{
 const s=raw.slice(i*3,i*3+3);
 return s==="---"?null:[Number(s[0]),s[1]==="R",s.charCodeAt(2)-65];
});
const bits={A:[1,0],M:[1,1,0,1,0]};
const rightOut={A:[0,1],M:[0,1,0,1,1]};
const carry={
 eleven:{A:[[],"elevenZeroOne"],M:[["M"],"eleven"]},
 elevenZeroOne:{A:[["M"],"one"],M:[["M","A"],"eleven"]},
 one:{A:[["A"],"one"],M:[["A","A"],"eleven"]}
};
const carryCost={eleven:4,elevenZeroOne:6,one:3};
const carryRight={
 eleven:[1,0,1,0],
 elevenZeroOne:[0,1,1,0,1,0],
 one:[0,1,0]
};
const leftCost={A:2,M:5}, rightCost={A:6,M:15};
const concat=x=>x.flatMap(c=>bits[c]);
const outputBits=x=>concat(x.slice().reverse());
const sumCost=(x,m)=>x.reduce((s,c)=>s+m[c],0);
function fold(x){
 let state="eleven",out=[];
 for(const ch of x){
  const [emit,next]=carry[state][ch];
  out.push(...emit);state=next;
 }
 return {state,out};
}
function runSource(q,l,r,steps){
 for(let t=0;t<steps;t++){
  const bit=l[0],ins=T[2*q+bit];
  if(ins===null||bit===undefined)
   return {error:"undefined transition",t,q,bit};
  const [write,right,next]=ins;
  if(right){
   const taken=r.shift();
   if(taken===undefined)return {error:"unknown right tape",t};
   l.shift();l.unshift(write);l.unshift(taken);
  }else{
   if(l.length===0)return {error:"unknown left tape",t};
   l.shift();r.unshift(write);
  }
  q=next;
 }
 return {q,l,r};
}
function compare(got,expect,kind,input){
 const a={q:expect.q,l:expect.l.join(""),r:expect.r.join("")};
 const b=got.error?got:{q:got.q,l:got.l.join(""),r:got.r.join("")};
 if(JSON.stringify(a)!==JSON.stringify(b))
  throw Error(JSON.stringify({kind,input,expected:a,actual:b}));
}
function firstTwoTurns(cs){
 const f=fold(cs),chunks=["M",...f.out],L=Array(50).fill(0),R=Array(50).fill(0);
 const duration=(4+4*sumCost(cs,leftCost))+13+
   sumCost(chunks,leftCost)+carryCost[f.state];
 const res=runSource(4,[1,0,...concat(cs),0,0,0,...L],
   [0,1,0,0,0,...R],duration);
 compare(res,{q:0,l:[0,...L],r:[...carryRight[f.state],...outputBits(chunks),...R]},
         "twoBlankTurns",cs.join(""));
 return f;
}
function anotherCycle(tok,chunks){
 const f=fold([...chunks,tok]);
 const L=Array(50).fill(0),R=Array(50).fill(0);
 const duration=sumCost([tok,...chunks],rightCost)+2+
   sumCost(f.out,leftCost)+carryCost[f.state];
 const res=runSource(0,[0,0,0,...L],
   [0,...bits[tok],...outputBits(chunks),0,0,...R],duration);
 compare(res,{q:0,l:[0,...L],
   r:[...carryRight[f.state],...outputBits(f.out),0,...R]},
   "anotherBlankCycle",tok+":"+chunks.join(""));
 return f;
}
function countRounds(cs){
 let f=firstTwoTurns(cs),state=f.state,word=["M",...f.out],n=0;
 while(state!=="eleven"&&n<100){
  const tok=state==="one"?"A":"M";
  f=anotherCycle(tok,word);
  state=f.state;word=f.out;n++;
 }
 if(state!=="eleven"||word[0]!=="M")
   throw Error("carry closure failed for "+cs.join(""));
 return n;
}
let first=0,cycles=0,maxRounds=0;
for(let n=0;n<=9;n++)for(let mask=0;mask<2**n;mask++){
 const cs=Array.from({length:n},(_,i)=>(mask>>i&1)?"M":"A");
 firstTwoTurns(cs);first++;
 for(const tok of ["A","M"]){anotherCycle(tok,cs);cycles++;}
 if(cs.includes("M")){
  const k=countRounds(cs);maxRounds=Math.max(maxRounds,k);
 }
}
console.log(JSON.stringify({
 table:raw,twoTurnCases:first,additionalCycleCases:cycles,
 maxAdditionalRounds:maxRounds,failures:0,
 source:"original partial transition table",status:"bounded verification only"
},null,2));
