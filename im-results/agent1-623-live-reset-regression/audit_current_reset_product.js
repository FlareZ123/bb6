#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");
const root = process.cwd();

const reset = JSON.parse(fs.readFileSync(path.join(
  root, "im-results/agent32-623-phase-automaton/ResetPatternDFA.json"), "utf8"));
const subset = JSON.parse(fs.readFileSync(path.join(
  root, "im-results/agent27-623-root-scan/PairCarrySynchronizingSubsetDFA.json"), "utf8"));
const post = JSON.parse(fs.readFileSync(path.join(
  root, "im-results/agent49-parity623/ResetPostStateDFA.json"), "utf8")).post_reset_pair;
const edges = JSON.parse(fs.readFileSync(path.join(
  root, "im-results/agent48-623-tight-window/SWindowEdgeRecords.json"), "utf8"));

const accepting = new Set(reset.accepting_states);
const B1 = new Set([
  10,11,12,70,71,72,82,83,84,88,89,90,115,116,117,
  151,152,153,160,161,162,169,170,171,181,182,183,187,188,189
]);

const odd = x => (x & 1n) === 1n;
function mod(a,m){ let r=a%m; return r<0n ? r+m : r; }

function evalA(a,k,m){
  for(;;){
    const q=k/3n, r=k%3n;
    if(r===2n) return [a+1n,q,m];
    if(a===0n){
      if(r===0n) return null;
      return [0n,q,m];
    }
    if(r===0n) return [a-1n,q,m+2n];
    a -= 1n;
    m += 2n*q + 3n;
    k = q;
  }
}

function drainB(a,b,d){
  while(b>0n){
    const old=b;
    const z=evalA(a,b-1n,d+2n*b+3n);
    if(z===null || z[1]>=old) return null;
    [a,b,d]=z;
  }
  return [a,d];
}

function highLevelNext(a,d){
  if(a===0n) return odd(d) ? drainB(d+1n,2n,2n) : [d,7n];
  if(odd(d) && a>=d+5n) return drainB(a-d-5n,d+3n,5n);
  if(!odd(d) && a>=d+3n) return drainB(a-d-2n,d+2n,2n);
  if(odd(a)) return null;
  if(a===d+2n) return drainB(0n,a,2n);
  if(odd(d)) return drainB(d+4n-a,a-1n,3n);
  const z=evalA(d+1n-a,a,2n*a+5n);
  return z===null ? null : drainB(...z);
}

function sectorData(a,d){
  let q,p,sector;
  if(a>=d){ q=d; p=a-d; sector=odd(d)?"LO":"LE"; }
  else { q=a; p=d-a; sector=odd(d)?"RO":"RE"; }
  const g=p-3n*q;
  const gamma={LO:18n,LE:10n,RO:2n,RE:4n}[sector];
  return {a,d,q,S:a+d,g,gamma,x:2n*g-gamma,y:6n*q,sector};
}

function ellOf(v){
  let ell=0, power=1n;
  while((power-1n)/2n < v+3n){ ell++; power*=3n; }
  return ell;
}

function windowIndices(S){
  const ell=ellOf(S);
  const B=34*ell+122;
  let k=0,p=1;
  while(p<=B){ p*=3; k++; }
  let j=0,p3=1n;
  const target=BigInt(B)**3n;
  while(p3<=target){ p3*=3n; j++; }
  return {ell,B,k,j};
}

function digitAt(z,i){
  return Number(mod(z/(3n**BigInt(i)),3n));
}

function runReset(word){
  let s=reset.initial_state, first=null;
  for(let i=0;i<word.length;i++){
    s=reset.transitions[s][word[i]];
    if(first===null && accepting.has(s)) first=i+1;
  }
  return first;
}

function runSubset(word){
  let s=subset.initial_state;
  for(const z of word) s=subset.image_subset_transitions[s][z];
  return s;
}

function runPost(word){
  let s=post.initial_state;
  for(const z of word) s=post.transitions[s][z];
  return post.outputs[s];
}

let a=0n,d=7n;
let transitions=0, nonsync=0, b1=0;
const failures=[];

for(let n=0;n<=10000;n++){
  const z=highLevelNext(a,d);
  if(z===null) throw new Error("source recurrence failed at D"+n);
  const target=sectorData(z[0],z[1]);

  if(n>=33){
    transitions++;
    const w=windowIndices(target.S);
    const word=[];
    for(let i=w.k+2;i<w.j-2;i++)
      word.push(3*digitAt(target.x,i)+digitAt(target.y,i));

    const first=runReset(word);
    if(first===null){
      failures.push({n,target:n+1,sector:target.sector,k:w.k,j:w.j,word,
        postResetOutput:runPost(word)});
    }else{
      const suffix=word.slice(first);
      const state=runSubset(suffix);
      const rank=subset.image_subset_states[state].length;
      if(rank>1) nonsync++;
      if(B1.has(state)) b1++;
    }
  }

  if(n===10000) break;
  [a,d]=z;
}

const edge653=edges.edges.find(e=>e[0]===653);
if(!edge653) throw new Error("SWindowEdgeRecords has no target 653");
const expected=[3,7,5,3,1,5,6,6,7,5,5,5];
if(failures.length<1 || failures[0].n!==652 ||
   JSON.stringify(failures[0].word)!==JSON.stringify(expected)){
  throw new Error("D653 regression changed; inspect current artifacts");
}

console.log(JSON.stringify({
  transitions,
  resetFailures:failures.length,
  failures,
  nonsynchronizingAcceptedSuffixes:nonsync,
  B1AcceptedSuffixes:b1,
  edge653
},null,2));
