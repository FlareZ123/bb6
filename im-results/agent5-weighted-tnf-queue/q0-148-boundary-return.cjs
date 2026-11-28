#!/usr/bin/env node
"use strict";
/**
 * Experimental exact first-return map for the q0-148 F1-open machine.
 * This is a finite check of a parametric CONJECTURE, NOT a universal proof.
 *
 * Input: E1 at penultimate A of finite tape word
 *   A^a B A^g1 B ... B A^g_(m-1) B A^4,
 * A=10 B=110, odd number m of B, a in {1,3},
 * each interior g_i odd >= 3, blank outside.
 *
 * Predicted first positive E1 section (and head index):
 *   m=1: [7, 1] for a=1, [7,1,1,1] for a=3, head A-index5 in group0.
 *   m>=3: [g1+g2+3, g3,...,g_(m-1), 3, 1^(a+1)],
 *          head A-index g1+2 in group0.
 *
 * Source transitions, unknown F1 and table are checked literally below.
 */
const RAW="1RB1LC1RC0RE0LA0LD1LA0RF1RB1RD0RC---";
const T=Array.from({length:12},(_,i)=>{
 const x=RAW.slice(i*3,i*3+3);
 return x==="---"?null:[Number(x[0]),x[1]==="R"?1:-1,x.charCodeAt(2)-65];
});
function encode(g){return g.slice(0,-1).map(k=>"10".repeat(k)+"110").join("")+"10".repeat(g.at(-1))}
function decode(s,p){
 let at=0,g=[0],mark=null;
 while(at<s.length){
  if(s.startsWith("110",at)){g.push(0);at+=3;}
  else if(s.startsWith("10",at)){
   if(at===p)mark={k:g.length-1,j:g.at(-1)};
   g[g.length-1]++;at+=2;
  } else return null;
 }
 return {g,mark};
}
function expected(g){
 const m=g.length-1,a=g[0];
 if(m===1)return {g:[7,...Array(a===1?1:3).fill(1)],mark:{k:0,j:5}};
 return {g:[g[1]+g[2]+3,...g.slice(3,-1),3,...Array(a+1).fill(1)],
         mark:{k:0,j:g[1]+2}};
}
function next(g,limit=300000){
 const s=encode(g),one=new Set();
 for(let i=0;i<s.length;i++)if(s[i]==="1")one.add(i);
 let q=4,x=s.length-4;
 for(let t=0;t<limit;t++){
  const bit=one.has(x)?1:0;
  if(t>0&&q===4&&bit===1){
   const low=Math.min(...one),high=Math.max(...one);
   let word="";
   for(let j=low;j<=high+1;j++)word+=one.has(j)?"1":"0";
   return {status:"E1",steps:t,observed:decode(word,x-low),
           neighborRight:one.has(x+1)?1:0};
  }
  const tr=T[2*q+bit];
  if(tr===null)return {status:"HALT",steps:t,q,bit};
  const [write,dir,nq]=tr;
  if(write)one.add(x);else one.delete(x);
  x+=dir;q=nq;
 }
 return {status:"CAPPED"};
}
function main(){
 let checked=0,longest=0,failed=[],perSize={};
 function test(g){
  const e=expected(g),r=next(g);
  checked++;
  let m=g.length-1,rec=perSize[m]||(perSize[m]={checked:0,maxSteps:0});
  rec.checked++;
  const ok=r.status==="E1"&&r.neighborRight===0&&
    JSON.stringify(r.observed)===JSON.stringify(e);
  if(r.steps){longest=Math.max(longest,r.steps);
    rec.maxSteps=Math.max(rec.maxSteps,r.steps);}
  if(!ok&&failed.length<12)failed.push({g,expected:e,observed:r});
 }
 for(const m of [1,3,5])for(const a of [1,3]){
  function recurse(g){
   if(g.length===m){test([...g,4]);return;}
   for(const v of [3,5,7])recurse([...g,v]);
  }
  recurse([a]);
 }
 let seed=0x0148c0de;
 function random(){
  seed ^= seed<<13;seed ^= seed>>>17;seed ^= seed<<5;
  return seed>>>0;
 }
 for(const m of [7,9])for(const a of [1,3])for(let t=0;t<200;t++){
  let g=[a];for(let k=1;k<m;k++)g.push(3+2*(random()%9));g.push(4);
  test(g);
 }
 console.log(JSON.stringify({
  table:RAW,grammar:"a in {1,3}, odd m, odd interior gaps >=3, final gap=4",
  tested:checked,perSize,longest,failures:failed,
  classification:"bounded experiment; parametric source return conjecture UNPROVED",
  rng:"xorshift32 seed=0x0148c0de"
 },null,2));
 if(failed.length)process.exitCode=1;
}
main();
