#!/usr/bin/env node
"use strict";
/**
 * Deterministic exact-source regression of the q0-148 complete
 * boundary-to-boundary gap-vector recurrence. Finite EXHAUST, not proof
 * of an unbounded number of markers.
 *
 * A=10, B=110, g=[a,g1,...,g_(m-1),4] encodes W=A^a B A^g1 ... B A^4.
 * At start/end E1 scans penultimate A of trailing A^4.
 * Boundary grammar:
 *   odd m>=3, a in {1,3}; each interior gap odd >=3;
 *   adjacent interior gaps drop by 0 or 2;
 *   g_(m-1) in {3,5};
 *   g1 in {m+a-3,m+a-1}.
 * Base exception: [3,4] -> [3,3,3,4].
 *
 * Conjectured complete next boundary:
 *   m' = m if a=1 else m+2;
 *   a' = g1-m+3 if a=1 else g1-m+1;
 *   b=[a',g2+2,...,g_(m-1)+2,5,4] if a=1
 *   b=[a',g2+2,...,g_(m-1)+2,5,3,3,4] if a=3.
 *
 * The gap-vector recurrence PRESERVES the grammar algebraically.
 * Its correspondence to the Turing machine still needs a universal proof.
 */
const code="1RB1LC1RC0RE0LA0LD1LA0RF1RB1RD0RC---";
const table=Array.from({length:12},(_,i)=>{
 const t=code.slice(3*i,3*i+3);
 return t==="---"?null:[Number(t[0]),t[1]==="R"?1:-1,t.charCodeAt(2)-65];
});
function encode(g){
 return g.slice(0,-1).map(k=>"10".repeat(k)+"110").join("")+"10".repeat(g.at(-1));
}
function parse(word,p){
 let i=0,g=[0],head=null;
 while(i<word.length){
  if(word.startsWith("110",i)){g.push(0);i+=3;}
  else if(word.startsWith("10",i)){
   if(i===p)head={k:g.length-1,j:g.at(-1)};
   g[g.length-1]++;i+=2;
  }else return null;
 }
 return {g,head};
}
function predict(g){
 const m=g.length-1,a=g[0];
 if(m===1){
  if(a!==3||g[1]!==4)throw Error("only source base [3,4]");
  return [3,3,3,4];
 }
 const nextA=g[1]-m+(a===1?3:1);
 return a===1?
   [nextA,...g.slice(2,-1).map(x=>x+2),5,4]:
   [nextA,...g.slice(2,-1).map(x=>x+2),5,3,3,4];
}
function isBoundary(g){
 const m=g.length-1,a=g[0];
 if(m===1)return a===3&&g[1]===4;
 if(m<3||m%2!==1||![1,3].includes(a)||g[m]!==4)return false;
 if(![m+a-3,m+a-1].includes(g[1]))return false;
 if(![3,5].includes(g[m-1]))return false;
 for(let i=1;i<m;i++)
  if(g[i]<3||g[i]%2!==1||(i<m-1&&![0,2].includes(g[i]-g[i+1])))
   return false;
 return true;
}
function nextBoundary(g,limit=120000){
 const w=encode(g),one=new Set();
 for(let i=0;i<w.length;i++)if(w[i]==="1")one.add(i);
 let q=4,x=w.length-4;
 for(let t=0;t<limit;t++){
  const a=one.has(x)?1:0;
  if(t>0&&q===4&&a===1){
   const low=Math.min(...one),high=Math.max(...one);
   if(x===high-2){
    let word="";
    for(let i=low;i<=high+1;i++)word+=one.has(i)?"1":"0";
    const parsed=parse(word,x-low);
    return {status:"boundary",t,g:parsed?.g??null,
            head:parsed?.head??null};
   }
  }
  const tr=table[2*q+a];
  if(tr===null)return {status:"haltingF1",t,x,q,a};
  const [w,dx,nq]=tr;
  if(w)one.add(x);else one.delete(x);
  x+=dx;q=nq;
 }
 return {status:"capped",steps:limit};
}
function main(){
 const results={target:code,cases:0,maxSteps:0,byMarker:{},failures:[],
   status:"bounded exact-source experiment; universal theorem pending"};
 function check(g){
  if(!isBoundary(g))throw Error("invalid boundary input: "+JSON.stringify(g));
  const p=predict(g),r=nextBoundary(g);
  results.cases++;
  const m=g.length-1,rec=results.byMarker[m]??(results.byMarker[m]={cases:0,maxSteps:0});
  rec.cases++;
  const ok=r.status==="boundary"&&
    JSON.stringify(r.g)===JSON.stringify(p)&&isBoundary(r.g)&&
    r.head?.k===r.g.length-1&&r.head?.j===2;
  if(r.t){rec.maxSteps=Math.max(rec.maxSteps,r.t);
    results.maxSteps=Math.max(results.maxSteps,r.t)}
  if(!ok&&results.failures.length<20)
   results.failures.push({g,expected:p,observed:r});
 }
 check([3,4]);
 // All 0/2 adjacent differences, penultimate gap 3 or 5; filter by
 // the EXACT relational invariant. No random sampling in this test.
 for(const m of [3,5,7,9,11])for(const a of [1,3]){
  function genBackward(rev){
   const index=(m-1)-rev.length;
   if(index===0){
    const g=[a,...rev.slice().reverse(),4];
    if(isBoundary(g))check(g);
    return;
   }
   const prev=rev.at(-1);
   for(const diff of [0,2])genBackward([...rev,prev+diff]);
  }
  for(const last of [3,5])genBackward([last]);
 }
 console.log(JSON.stringify(results,null,2));
 if(results.failures.length)process.exitCode=1;
}
main();
