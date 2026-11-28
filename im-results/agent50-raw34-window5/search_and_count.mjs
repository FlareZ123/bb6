#!/usr/bin/env node
/**
 * Deterministic radius-two physical Raw34 invariant-family discovery.
 *
 * This is untrusted candidate generation, NOT the proof of nonhalting.
 * Its bitmasks and 25-action product domains are checked by the
 * separately compiled original-tape Lean theorem Window5Domains.lean.
 *
 * Run from the repo root:
 *   node im-results/agent50-raw34-window5/search_and_count.mjs
 *
 * A repeat run reconstructs and compares every retained bitmask and
 * exact older-source marginal count in mask-bank-128.json.
 */
import assert from "node:assert/strict";
import {readFileSync} from "node:fs";
import {dirname,resolve} from "node:path";
import {fileURLToPath} from "node:url";

const dir=dirname(fileURLToPath(import.meta.url));
const first=resolve(dir,"../agent50-raw34-firsthole");
const depth2=JSON.parse(readFileSync(resolve(first,"depth2-candidate-witnesses.json"),"utf8")).second_level;
const depth3=JSON.parse(readFileSync(resolve(first,"depth3-candidate-witnesses.json"),"utf8")).witnesses;
assert.equal(depth2.length,74);
assert.equal(depth3.length,1206);

const actions=["HALT"];
for(const w of "01")for(const d of "LR")for(const q of "ABCDEF")
  actions.push(w+d+q);
const index=new Map(actions.map((v,i)=>[v,i]));
const full=(1<<25)-1;
const bit=x=>1<<index.get(x);
const mask=a=>a.reduce((m,x)=>m|bit(x),0);
const slots=[7,5,3,1,8,9,10,11]; // physical D1,C1,B1,A1,E0,E1,F0,F1
const parse=t=>{
  const s=t.replaceAll("_","").match(/.{3}/g);
  assert.equal(s.length,12);
  return slots.map(i=>s[i]==="---"?full:bit(s[i]==="HLT"?"HALT":s[i]));
};
function given(...pairs){
  const a=Array(8).fill(full);
  for(const [i,v] of pairs)a[i]=bit(v);
  return a;
}
function moves(states){
  const a=[];
  for(const w of "01")for(const d of "LR")for(const q of states)
    a.push(w+d+q);
  return a;
}
const bank=[];
bank.push(...("0LA 0LB 0LC 0RA 0RB 0RC 0RD 1LC 1RA 1RB 1RC"
  .split(" ").map(v=>given([0,v]))));
bank.push(...depth2.map(x=>parse(x.table)));
bank.push(parse("1RB---_1RC---_0RD1LC_1LC1RD_------_------"));
for(const c of moves("CD"))for(const d of moves("CD"))
  bank.push(given([0,d],[1,c]));
bank.push(...depth3.map(x=>parse(x.table)));
for(const b of moves("BCD"))for(const c of moves("BCD"))for(const d of moves("BCD"))
  bank.push(given([0,d],[1,c],[2,b]));
for(const p of [
  "1RB1LD_1RC---_0RD0RA_1LC1RD_------_------",
  "1RB---_1RC---_0RD0RE_1LC1RD_---1LD_------",
  "1RB---_1RC---_0RD0LD_1LC0RE_1RD---_------"
])bank.push(parse(p));
assert.equal(bank.length,3087);
for(const S of ["CDE","CDF","CDEF","BCDE","BCDF","BCDEF",
                "ABCD","ABCDE","ABCDF"]){
  const p=Array(8).fill(full),domain=mask(moves(S));
  for(const [i,q] of [[0,"D"],[1,"C"],[2,"B"],[3,"A"],
                       [4,"E"],[5,"E"],[6,"F"],[7,"F"]])
    if(S.includes(q))p[i]=domain;
  bank.push(p);
}
assert.equal(bank.length,3096);

const N=192,S=32;
const successor=Array.from({length:25},()=>new Int16Array(2*N));
for(let a=1;a<25;a++){
  const v=actions[a],w=Number(v[0]),right=v[1]==="R",q="ABCDEF".indexOf(v[2]);
  for(let u=0;u<N;u++){
    const x=u%S,ar=Array.from({length:5},(_,j)=>(x>>(4-j))&1);
    for(let f=0;f<2;f++){
      const after=right?[...ar.slice(1),f]:[f,...ar.slice(0,-1)];
      after[right?1:3]=w;
      successor[a][2*u+f]=q*S+after.reduce((n,b)=>n*2+b,0);
    }
  }
}
let seed=987654321;
function random(){
  seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;
  return (seed>>>0)/4294967296;
}

const p=["1RB",null,"1RC",null,"0RD",null,"1LC",null,
         "HALT",null,"HALT","HALT"].map(v=>v==null?0:index.get(v));
const variable=[1,3,5,7,9],families=new Map();
let closedWithE1AbstractRead=0,closedNontrivial=0;
const trials=250000;
for(let j=0;j<trials;j++){
  for(const slot of variable)p[slot]=1+Math.floor(random()*24);
  const seen=new Uint8Array(N),queue=[0];
  let valid=true,queriedSlots=0;seen[0]=1;
  for(let k=0;k<queue.length;k++){
    const u=queue[k],slot=2*Math.floor(u/S)+((u>>2)&1),a=p[slot];
    queriedSlots|=1<<slot;
    if(a===0){valid=false;break;}
    const next=successor[a];
    for(let f=0;f<2;f++){
      const v=next[2*u+f];
      if(!seen[v]){seen[v]=1;queue.push(v);}
    }
  }
  if(!valid||!(queriedSlots&(1<<9)))continue;
  closedWithE1AbstractRead++;
  const domainMasks=[];
  for(const slot of slots){
    const q=Math.floor(slot/2),scanned=slot%2,window=[];
    for(let u=q*S;u<(q+1)*S;u++)
      if(seen[u]&&((u>>2)&1)===scanned)window.push(u);
    if(!window.length){domainMasks.push(full);continue;}
    let allowed=0;
    for(let a=1;a<25;a++){
      const next=successor[a];
      let good=true;
      for(const u of window)
        if(!seen[next[2*u]]||!seen[next[2*u+1]]){good=false;break;}
      if(good)allowed|=1<<a;
    }
    assert.notEqual(allowed,0);
    domainMasks.push(allowed);
  }
  // A fully old/graph-covered product cannot add new physical completions.
  if(bank.some(row=>row.every((v,k)=>(v&domainMasks[k])===domainMasks[k])))
    continue;
  closedNontrivial++;
  const key=domainMasks.join(",");
  if(families.has(key))continue;
  let bits=0n;
  for(const u of queue)bits|=1n<<BigInt(u);
  const sourceTable=Array.from({length:6},(_,i)=>
    [p[2*i],p[2*i+1]]
    .map(c=>c===0?"HALT":actions[c]).join("")).join("_");
  families.set(key,{maskHex:"0x"+bits.toString(16),
    sourceTable,nWindows:queue.length,domainMasks});
}

function exactMarginal(domainMasks){
  const choices=domainMasks.map(v=>actions.map((_,i)=>i).filter(i=>v&(1<<i)));
  const pow=Array(9).fill(1n);
  for(let k=7;k>=0;k--)pow[k]=pow[k+1]*BigInt(choices[k].length);
  const active=bank.map((row,i)=>
    row.every((v,k)=>v&domainMasks[k])?i:-1).filter(i=>i>=0);
  const memo=new Map();
  function count(ids,k){
    if(!ids.length)return 0n;
    if(k===8)return 1n;
    if(ids.some(id=>bank[id].slice(k).every((v,j)=>
        (v&domainMasks[k+j])===domainMasks[k+j])))return pow[k];
    const key=k+":"+ids.join(",");
    if(memo.has(key))return memo.get(key);
    let n=0n;
    for(const x of choices[k])
      n+=count(ids.filter(id=>bank[id][k]&(1<<x)),k+1);
    memo.set(key,n);
    return n;
  }
  return {grossPhysical:pow[0].toString(),
    outsideBase:(pow[0]-count(active,0)).toString()};
}
const ranked=[];
for(const family of families.values()){
  const arithmetic=exactMarginal(family.domainMasks);
  if(BigInt(arithmetic.outsideBase)>0n)
    ranked.push({...family,...arithmetic});
}
ranked.sort((a,b)=>
  BigInt(b.outsideBase)>BigInt(a.outsideBase)?1:
  BigInt(b.outsideBase)<BigInt(a.outsideBase)?-1:0);
assert.equal(closedWithE1AbstractRead,4835);
assert.equal(closedNontrivial,4519);
assert.equal(families.size,2592);
assert.equal(ranked.length,1158);
assert.equal(ranked[0].maskHex,"0xf000f000fffffffffffffccccccccfcc00000001");
assert.equal(ranked[0].outsideBase,"2835000");

const stored=JSON.parse(readFileSync(resolve(dir,"mask-bank-128.json"),"utf8"));
assert.equal(stored.seed,987654321);
assert.equal(stored.trials,trials);
assert.equal(stored.closedWithE1AbstractRead,closedWithE1AbstractRead);
assert.equal(stored.closedNontrivial,closedNontrivial);
assert.equal(stored.uniqueNontrivialFamilies,families.size);
assert.equal(stored.positiveOutsideOldGraph,ranked.length);
assert.equal(stored.retained,128);
assert.deepEqual(stored.ranked,ranked.slice(0,128));
console.log(JSON.stringify({
  status:"PASS: deterministic Raw34 radius-two finite-search and BigInt-domain census",
  seed:stored.seed,trials,
  sourceBank:bank.length,
  positiveFamilies:ranked.length,retained:stored.retained,
  bestMask:ranked[0].maskHex,
  bestGross:ranked[0].grossPhysical,
  bestOldBankMarginal:ranked[0].outsideBase
},null,2));
