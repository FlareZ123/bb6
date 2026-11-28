#!/usr/bin/env node
"use strict";
/*
 * EXPERIMENTAL (not a proof): boundary grammar for the q0-148 F1 holdout.
 * Machine: A0 1RB, A1 1LC, B0 1RC, B1 0RE, C0 0LA, C1 0LD,
 *          D0 1LA, D1 0RF, E0 1RB, E1 1RD, F0 0RC, F1 HALT.
 *
 * Token A = 10, B = 110. Initial section language:
 *   A^a B A^b1 B ... B A^c,
 * a>=0, internal b_j>=1, terminal c>=2,
 * head E at the first bit of the last two A tokens.
 *
 * Checks only finite exhaustive grids; it does NOT certify the universal
 * return lemma. Every return is checked against the physical tape contents.
 */
const TABLE = "1RB1LC1RC0RE0LA0LD1LA0RF1RB1RD0RC---";
const rules=Array.from({length:12},(_,i)=>{
 const t=TABLE.slice(3*i,3*i+3);
 return t==="---"?null:[Number(t[0]),t[1]==="R"?1:-1,t.charCodeAt(2)-65];
});
const tok = {A:"10",B:"110"};
const fromGaps = g => g.slice(0,-1).map(n=>tok.A.repeat(n)+tok.B).join("")+tok.A.repeat(g.at(-1));
function toGaps(word){
 let i=0,g=[],k=0;
 while(i<word.length){
  if(word.startsWith(tok.B,i)){g.push(k);k=0;i+=3}
  else if(word.startsWith(tok.A,i)){k++;i+=2}
  else return null;
 }
 g.push(k);
 return g;
}
function closed(g){return Array.isArray(g)&&g.at(-1)>=2&&g.slice(1,-1).every(x=>x>=1)}
function firstReturn(g,maxSteps){
 const w=fromGaps(g),tape=new Set();
 for(let i=0;i<w.length;i++)if(w[i]==="1")tape.add(i);
 let q=4,x=w.length-4,left=0,right=w.length-1;
 if(!tape.has(x)||tape.has(x+1)||!closed(g))throw Error("invalid input");
 for(let t=0;t<maxSteps;t++){
  const a=tape.has(x)?1:0;
  if(t>0&&q===4&&a===1&&x===right-3){
   const lo=Math.min(...tape),hi=Math.max(...tape);
   let word="";
   for(let j=lo;j<=hi+1;j++)word+=tape.has(j)?"1":"0";
   const result=toGaps(word);
   const physical=(x===hi-2&&hi===right-1&&lo===left);
   return {status:"return",steps:t,closed:closed(result),physical,
           result,resultLength:word.length};
  }
  const ins=rules[2*q+a];
  if(!ins)return {status:"halt",steps:t,head:x,state:q,read:a};
  const [write,move,next]=ins;
  if(write)tape.add(x);else tape.delete(x);
  x+=move;q=next;left=Math.min(left,x);right=Math.max(right,x);
 }
 return {status:"cap",steps:maxSteps};
}
function run(maxB=4,maxSteps=200000){
 const totals={inputFamily:"A^a B (A^b B)* A^c; a in 0..4, b in 1..4, c in 2..6",
  maxB,maxSteps,checked:0,returned:0,closed:0,physical:0,halt:0,capped:0,
  strongestTime:0,failures:[]};
 for(let n=1;n<=maxB;n++){
  function descend(g){
   if(g.length===n){
    for(let last=2;last<=6;last++){
     const sample=[...g,last],v=firstReturn(sample,maxSteps);
     totals.checked++;totals.strongestTime=Math.max(totals.strongestTime,v.steps);
     if(v.status==="return"){totals.returned++;if(v.closed)totals.closed++;
       if(v.physical)totals.physical++}
     else if(v.status==="halt")totals.halt++;
     else totals.capped++;
     if(v.status!=="return"||!v.closed||!v.physical){
       if(totals.failures.length<10)totals.failures.push({sample,result:v});
     }
    }
    return;
   }
   for(let b=1;b<=4;b++)descend([...g,b]);
  }
  for(let a=0;a<=4;a++)descend([a]);
 }
 console.log(JSON.stringify(totals,null,2));
 if(totals.failures.length)process.exitCode=1;
}
const maxB=Number(process.argv[2]||4);
const maxSteps=Number(process.argv[3]||200000);
if(!Number.isInteger(maxB)||maxB<1||maxB>6||!Number.isInteger(maxSteps)||maxSteps<1){
 throw Error("usage: node q0-148-boundary-grammar.cjs [maxB=4] [maxSteps=200000]");
}
run(maxB,maxSteps);
