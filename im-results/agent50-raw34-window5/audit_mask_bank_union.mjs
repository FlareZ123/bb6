#!/usr/bin/env node
/**
 * Independent 25-ary reduced-MDD exact union for 128 sound *candidate*
 * radius-two Raw34 window families against 3,087 source-accepted
 * classical cylinders + nine source-accepted closed-control families.
 *
 * The candidate source theorem is Window5Domains.lean. The finite
 * search/census reconstructed independently by search_and_count.mjs.
 * These numbers are NOT a global or complete Raw34 Cover.
 *
 * Run:
 *   node im-results/agent50-raw34-window5/audit_mask_bank_union.mjs
 */
import assert from "node:assert/strict";
import {readFileSync} from "node:fs";
import {dirname,resolve} from "node:path";
import {fileURLToPath} from "node:url";
const dir=dirname(fileURLToPath(import.meta.url));
const first=resolve(dir,"../agent50-raw34-firsthole");
const depth2=JSON.parse(readFileSync(resolve(first,"depth2-candidate-witnesses.json"),"utf8")).second_level;
const depth3=JSON.parse(readFileSync(resolve(first,"depth3-candidate-witnesses.json"),"utf8")).witnesses;
const maskBank=JSON.parse(readFileSync(resolve(dir,"mask-bank-128.json"),"utf8"));
const efBank=JSON.parse(readFileSync(resolve(dir,"ef-conjugate-bank-128.json"),"utf8"));
const actions=["HALT"];
for(const w of "01")for(const d of "LR")for(const q of "ABCDEF")
  actions.push(w+d+q);
const index=new Map(actions.map((v,i)=>[v,i]));
const FULL=(1<<25)-1,bit=v=>1<<index.get(v);
const mask=arr=>arr.reduce((v,x)=>v|bit(x),0);
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
const cylinders=[];
cylinders.push(...("0LA 0LB 0LC 0RA 0RB 0RC 0RD 1LC 1RA 1RB 1RC"
  .split(" ").map(v=>given([0,v]))));
cylinders.push(...depth2.map(x=>parse(x.table)));
cylinders.push(parse("1RB---_1RC---_0RD1LC_1LC1RD_------_------"));
for(const c of moves("CD"))for(const d of moves("CD"))
  cylinders.push(given([0,d],[1,c]));
cylinders.push(...depth3.map(x=>parse(x.table)));
for(const b of moves("BCD"))for(const c of moves("BCD"))for(const d of moves("BCD"))
  cylinders.push(given([0,d],[1,c],[2,b]));
for(const p of [
  "1RB1LD_1RC---_0RD0RA_1LC1RD_------_------",
  "1RB---_1RC---_0RD0RE_1LC1RD_---1LD_------",
  "1RB---_1RC---_0RD0LD_1LC0RE_1RD---_------"
])cylinders.push(parse(p));
assert.equal(cylinders.length,3087);
const graph=[];
for(const S of ["CDE","CDF","CDEF","BCDE","BCDF","BCDEF",
                "ABCD","ABCDE","ABCDF"]){
  const p=Array(8).fill(FULL),allowed=mask(moves(S));
  for(const [i,q] of [[0,"D"],[1,"C"],[2,"B"],[3,"A"],
                       [4,"E"],[5,"E"],[6,"F"],[7,"F"]])
    if(S.includes(q))p[i]=allowed;
  graph.push(p);
}
assert.equal(graph.length,9);
assert.equal(maskBank.ranked.length,128);
assert.equal(efBank.conjugates.length,128);
// Verify every E/F conjugate is mechanically derived, not blindly
// accepted from a JSON record. The physical HALT action remains 0.
function conjugateAction(i){
  if(i===0)return 0;
  const a=actions[i],q=a[2]==="E"?"F":a[2]==="F"?"E":a[2];
  return index.get(a.slice(0,2)+q);
}
function conjugateDomain(bits){
  let out=0;
  for(let i=0;i<25;i++)
    if(bits&(1<<i))out|=1<<conjugateAction(i);
  return out;
}
function conjugateMask(hex){
  const old=BigInt(hex),section=(1n<<32n)-1n;
  const e=(old>>128n)&section,f=(old>>160n)&section;
  return "0x"+((old&((1n<<128n)-1n))|(f<<128n)|(e<<160n)).toString(16);
}
for(const [i,record] of efBank.conjugates.entries()){
  const old=maskBank.ranked[i],transformed=old.domainMasks.map(conjugateDomain);
  const domain=transformed.slice();
  domain[4]=transformed[6];domain[5]=transformed[7];
  domain[6]=transformed[4];domain[7]=transformed[5];
  assert.deepEqual(record.domainMasks,domain);
  assert.equal(record.maskHex,conjugateMask(old.maskHex));
  assert.equal(record.sourceIndex,i);
}

const nodes=[{at:8},{at:8}],unique=Array.from({length:8},()=>new Map());
function mk(at,ch){
  if(ch.every(x=>x===ch[0]))return ch[0];
  const key=ch.join(","),prev=unique[at].get(key);
  if(prev!==undefined)return prev;
  const id=nodes.length;
  nodes.push({at,ch:ch.slice()});
  unique[at].set(key,id);
  return id;
}
function join(a,b,memo){
  if(a===1||b===1)return 1;
  if(a===0)return b;
  if(b===0||a===b)return a;
  const lo=Math.min(a,b),hi=Math.max(a,b),key=lo+":"+hi;
  const cached=memo.get(key);
  if(cached!==undefined)return cached;
  const at=Math.min(nodes[a].at,nodes[b].at);
  const ch=Array.from({length:25},(_,i)=>
    join(nodes[a].at===at?nodes[a].ch[i]:a,
         nodes[b].at===at?nodes[b].ch[i]:b,memo));
  const out=mk(at,ch);
  memo.set(key,out);
  return out;
}
const union=(a,b)=>join(a,b,new Map());
function productBDD(domain){
  let r=1;
  for(let at=7;at>=0;at--){
    const v=domain[at];
    assert(Number.isInteger(v)&&v>0&&v<=FULL);
    const ch=Array.from({length:25},(_,i)=>(v&(1<<i))?r:0);
    r=mk(at,ch);
  }
  return r;
}
function sourceCubes(ps,at=0){
  if(!ps.length)return 0;
  if(at===8)return 1;
  const wild=[],by=Array.from({length:25},()=>[]);
  for(const p of ps){
    const v=p[at];
    if(v===FULL)wild.push(p);
    else{
      const i=Math.log2(v);
      assert(Number.isInteger(i),"old pattern must use one physical action per fixed slot");
      by[i].push(p);
    }
  }
  const w=sourceCubes(wild,at+1);
  if(w===1)return 1;
  return mk(at,Array.from({length:25},(_,i)=>
    union(w,sourceCubes(by[i],at+1))));
}
const pow=Array.from({length:9},(_,i)=>25n**BigInt(i));
const memo=new Map();
function cardinality(root,at=0){
  if(root===0)return 0n;
  if(root===1)return pow[8-at];
  const node=nodes[root];
  let val=memo.get(root);
  if(val===undefined){
    val=node.ch.reduce((n,v)=>n+cardinality(v,node.at+1),0n);
    memo.set(root,val);
  }
  return pow[node.at-at]*val;
}

let baseline=sourceCubes(cylinders);
for(const family of graph)baseline=union(baseline,productBDD(family));
const oldCount=cardinality(baseline);
assert.equal(oldCount,123226284000n);

let expanded=baseline;
const marginal=[];
for(const [i,item] of maskBank.ranked.entries()){
  const previous=cardinality(expanded);
  expanded=union(expanded,productBDD(item.domainMasks));
  const gain=cardinality(expanded)-previous;
  assert(gain>=0n);
  marginal.push({ordinal:i+1,mask:item.maskHex,gain:String(gain)});
}
const expandedCount=cardinality(expanded),gain=expandedCount-oldCount;
assert.equal(gain,51399300n);
assert.equal(expandedCount,123277683300n);
let expandedEF=expanded;
let positiveSymmetry=0;
for(const record of efBank.conjugates){
  const previous=cardinality(expandedEF);
  expandedEF=union(expandedEF,productBDD(record.domainMasks));
  if(cardinality(expandedEF)>previous)positiveSymmetry++;
}
const symmetryCount=cardinality(expandedEF),symmetryGain=symmetryCount-expandedCount;
assert.equal(symmetryGain,78216493n);
assert.equal(symmetryCount,123355899793n);
assert.equal(cardinality(expandedEF)+
  (25n**8n-cardinality(expandedEF)),25n**8n);

console.log(JSON.stringify({
  status:"PASS: exact 25-way MDD union arithmetic; nonhalting still conditional on original-source Lean gate",
  raw34Parent:"1RB---_1RC---_0RD---_1LC---_------_------",
  physicalParentMass:String(25n**8n),
  sourceCylinders:cylinders.length,graphFamilies:graph.length,
  radiusTwoInvariants:maskBank.ranked.length,
  oldPlusGraph:String(oldCount),withRadiusTwo:String(expandedCount),
  genuinelyOutsideOlderPortfolio:String(gain),
  stillUncoveredByTheseFamilies:String(25n**8n-expandedCount),
  efConjugateInvariants:efBank.conjugates.length,
  symmetryAdditionalPhysical:String(symmetryGain),
  bothBanksOutsideOlderPortfolio:String(symmetryCount-oldCount),
  bothBanksExactUnion:String(symmetryCount),
  bothBanksUncovered:String(25n**8n-symmetryCount),
  nonzeroSymmetryMasks:positiveSymmetry,
  mddNodes:nodes.length,nonzeroNovelMasks:marginal.filter(x=>BigInt(x.gain)>0n).length,
  firstMarginals:marginal.slice(0,20)
},null,2));
