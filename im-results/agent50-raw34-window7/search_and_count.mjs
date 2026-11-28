#!/usr/bin/env node
/*
 * Reproduce seven-cell Raw34 invariant search and its exact marginal
 * against the older 3,087 source-certificate cylinders, nine closed
 * graph families, and 256 radius-two product domains. This is an
 * UNTRUSTED finite search and exact census, NOT itself a theorem.
 * The source proof is Window7General.lean and the eight
 * Window7DomainShard*.lean physical action-domain checks.
 */
import assert from "node:assert/strict";
import {readFileSync} from "node:fs";
import {dirname,resolve} from "node:path";
import {fileURLToPath} from "node:url";
const dir=dirname(fileURLToPath(import.meta.url));
const first=resolve(dir,"../agent50-raw34-firsthole");
const b5dir=resolve(dir,"../agent50-raw34-window5");
const depth2=JSON.parse(readFileSync(resolve(first,"depth2-candidate-witnesses.json"),"utf8")).second_level;
const depth3=JSON.parse(readFileSync(resolve(first,"depth3-candidate-witnesses.json"),"utf8")).witnesses;
const bank5=JSON.parse(readFileSync(resolve(b5dir,"mask-bank-128.json"),"utf8")).ranked;
const symmetry5=JSON.parse(readFileSync(resolve(b5dir,"ef-conjugate-bank-128.json"),"utf8")).conjugates;
const expected=JSON.parse(readFileSync(resolve(dir,"mask-bank-128.json"),"utf8"));
const actions=["HALT"];
for(const w of "01")for(const d of "LR")for(const q of "ABCDEF")actions.push(w+d+q);
const index=new Map(actions.map((s,i)=>[s,i])),FULL=(1<<25)-1,bit=v=>1<<index.get(v);
const mask=arr=>arr.reduce((a,v)=>a|bit(v),0);
const slots=[7,5,3,1,8,9,10,11];
function parse(t){
  const s=t.replaceAll("_","").match(/.{3}/g);
  assert.equal(s.length,12);
  return slots.map(i=>s[i]==="---"?FULL:bit(s[i]==="HLT"?"HALT":s[i]));
}
function given(...pairs){
  const a=Array(8).fill(FULL);
  for(const [i,v] of pairs)a[i]=bit(v);
  return a;
}
function moves(S){
  const a=[];
  for(const w of "01")for(const d of "LR")for(const q of S)a.push(w+d+q);
  return a;
}
const bank=[];
bank.push(...("0LA 0LB 0LC 0RA 0RB 0RC 0RD 1LC 1RA 1RB 1RC".split(" ").map(v=>given([0,v]))));
bank.push(...depth2.map(x=>parse(x.table)),parse("1RB---_1RC---_0RD1LC_1LC1RD_------_------"));
for(const c of moves("CD"))for(const d of moves("CD"))bank.push(given([0,d],[1,c]));
bank.push(...depth3.map(x=>parse(x.table)));
for(const b of moves("BCD"))for(const c of moves("BCD"))for(const d of moves("BCD"))
  bank.push(given([0,d],[1,c],[2,b]));
for(const t of [
  "1RB1LD_1RC---_0RD0RA_1LC1RD_------_------",
  "1RB---_1RC---_0RD0RE_1LC1RD_---1LD_------",
  "1RB---_1RC---_0RD0LD_1LC0RE_1RD---_------"
])bank.push(parse(t));
assert.equal(bank.length,3087);
for(const S of ["CDE","CDF","CDEF","BCDE","BCDF","BCDEF","ABCD","ABCDE","ABCDF"]){
  const a=Array(8).fill(FULL),x=mask(moves(S));
  for(const [i,q] of [[0,"D"],[1,"C"],[2,"B"],[3,"A"],[4,"E"],[5,"E"],[6,"F"],[7,"F"]])
    if(S.includes(q))a[i]=x;
  bank.push(a);
}
const nodes=[{at:8},{at:8}],unique=Array.from({length:8},()=>new Map());
function mk(at,ch){
  if(ch.every(v=>v===ch[0]))return ch[0];
  const key=ch.join(","),hit=unique[at].get(key);
  if(hit!==undefined)return hit;
  const id=nodes.length;nodes.push({at,ch:ch.slice()});unique[at].set(key,id);return id;
}
function join(a,b,memo){
  if(a===1||b===1)return 1;
  if(a===0)return b;if(b===0||a===b)return a;
  const lo=Math.min(a,b),hi=Math.max(a,b),key=lo+","+hi;
  if(memo.has(key))return memo.get(key);
  const at=Math.min(nodes[a].at,nodes[b].at);
  const ch=Array.from({length:25},(_,i)=>
    join(nodes[a].at===at?nodes[a].ch[i]:a,
         nodes[b].at===at?nodes[b].ch[i]:b,memo));
  const r=mk(at,ch);memo.set(key,r);return r;
}
const union=(a,b)=>join(a,b,new Map());
function product(domain){
  let r=1;
  for(let i=7;i>=0;i--){
    const ch=Array.from({length:25},(_,j)=>(domain[i]&(1<<j))?r:0);
    r=mk(i,ch);
  }
  return r;
}
function initial(ps,at=0){
  if(!ps.length)return 0;
  if(at===8)return 1;
  const wild=[],by=Array.from({length:25},()=>[]);
  for(const p of ps){const v=p[at];if(v===FULL)wild.push(p);else by[Math.log2(v)].push(p);}
  const w=initial(wild,at+1);
  if(w===1)return 1;
  return mk(at,Array.from({length:25},(_,i)=>union(w,initial(by[i],at+1))));
}
let root=initial(bank.slice(0,3087));
for(const row of bank.slice(3087))root=union(root,product(row));
const pow=Array.from({length:9},(_,i)=>25n**BigInt(i)),countMemo=new Map();
function card(r,at=0){
  if(r===0)return 0n;
  if(r===1)return pow[8-at];
  const node=nodes[r];
  let v=countMemo.get(r);
  if(v===undefined){v=node.ch.reduce((n,x)=>n+card(x,node.at+1),0n);countMemo.set(r,v);}
  return pow[node.at-at]*v;
}
assert.equal(card(root),123226284000n);
for(const row of [...bank5,...symmetry5])root=union(root,product(row.domainMasks));
const baseline=card(root);
assert.equal(baseline,123355899793n);

// Radius-three state index is q*128 + 64*L3 + 32*L2 + 16*L1 +
// 8*scanned + 4*R1 + 2*R2 + R3. Newly entering bit branches both ways.
const R=3,K=7,S=1<<K,N=6*S,successor=Array.from({length:25},()=>new Int16Array(2*N));
for(let a=1;a<25;a++){
  const mv=actions[a],write=Number(mv[0]),right=mv[1]==="R",next="ABCDEF".indexOf(mv[2]);
  for(let u=0;u<N;u++){
    const x=u%S,arr=Array.from({length:K},(_,j)=>(x>>(K-j-1))&1);
    for(let f=0;f<2;f++){
      const y=right?[...arr.slice(1),f]:[f,...arr.slice(0,-1)];
      y[right?R-1:R+1]=write;
      successor[a][2*u+f]=next*S+y.reduce((n,b)=>n*2+b,0);
    }
  }
}
const p=["1RB",null,"1RC",null,"0RD",null,"1LC",null,
         "HALT",null,"HALT","HALT"].map(v=>v==null?0:index.get(v));
const randomSlots=[1,3,5,7,9];
let seed=8112019;
function random(){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return (seed>>>0)/4294967296;}
const families=new Map();
let hits=0;
const trials=100000;
for(let j=0;j<trials;j++){
  for(const slot of randomSlots)p[slot]=1+Math.floor(random()*24);
  const seen=new Uint8Array(N),queue=[0];
  let valid=true,queryMask=0;
  seen[0]=1;
  for(let k=0;k<queue.length;k++){
    const u=queue[k],slot=2*Math.floor(u/S)+((u>>R)&1),a=p[slot];
    queryMask|=1<<slot;
    if(a===0){valid=false;break;}
    const next=successor[a];
    for(let f=0;f<2;f++){const v=next[2*u+f];if(!seen[v]){seen[v]=1;queue.push(v);}}
  }
  if(!valid||!(queryMask&(1<<9)))continue;
  hits++;
  const domainMasks=[];
  for(const slot of slots){
    const q=Math.floor(slot/2),scanned=slot%2,windows=[];
    for(let u=q*S;u<(q+1)*S;u++)
      if(seen[u]&&((u>>R)&1)===scanned)windows.push(u);
    if(!windows.length){domainMasks.push(FULL);continue;}
    let domain=0;
    for(let a=1;a<25;a++){
      const next=successor[a];let ok=true;
      for(const u of windows)
        if(!seen[next[2*u]]||!seen[next[2*u+1]]){ok=false;break;}
      if(ok)domain|=1<<a;
    }
    assert.notEqual(domain,0);
    domainMasks.push(domain);
  }
  const key=domainMasks.join(",");
  if(families.has(key))continue;
  let mask=0n;
  for(const u of queue)mask|=1n<<BigInt(u);
  const sourceTable=Array.from({length:6},(_,i)=>
    [p[2*i],p[2*i+1]].map(x=>actions[x]).join("")).join("_");
  families.set(key,{windowMask:"0x"+mask.toString(16),domainMasks,
    nWindows:queue.length,sourceTable});
}
const positive=[];
for(const row of families.values()){
  const add=card(union(root,product(row.domainMasks)))-baseline;
  if(add>0n)positive.push({...row,individualOutside256:String(add),
    grossPhysical:String(row.domainMasks.reduce((a,b)=>{
      let n=0;for(let k=0;k<25;k++)n+=(b>>k)&1;
      return a*BigInt(n);
    },1n))});
}
positive.sort((a,b)=>BigInt(b.individualOutside256)>BigInt(a.individualOutside256)?1:
  BigInt(b.individualOutside256)<BigInt(a.individualOutside256)?-1:0);
let integrated=root,nonzero=0;
for(const row of positive.slice(0,128)){
  const before=card(integrated);
  integrated=union(integrated,product(row.domainMasks));
  if(card(integrated)>before)nonzero++;
}
assert.equal(hits,2159);
assert.equal(families.size,1504);
assert.equal(positive.length,319);
assert.equal(card(integrated)-baseline,15606675n);
assert.equal(nonzero,109);
assert.deepEqual(positive.slice(0,128),expected.ranked);
assert.equal(expected.newUnionCount,String(card(integrated)));
console.log(JSON.stringify({status:"PASS deterministic seven-cell BFS, original-action table, and exact 25-way union",
  seed:8112019,trials,hits,unique:families.size,positive:positive.length,
  sourceBank:bank.length,
  rootWithoutSeven:String(baseline),afterSeven:String(card(integrated)),
  freshOutsideOldPlus256:String(card(integrated)-baseline),
  retained:128,nonzeroRetained:nonzero},null,2));
