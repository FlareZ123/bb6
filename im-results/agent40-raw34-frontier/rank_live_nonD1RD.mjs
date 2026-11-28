#!/usr/bin/env node
/**
 * Exact 25-way proof-bank complement for Raw34 with D1 != 1RD.
 *
 * Unlike a flat total-machine scan, the DAG memoizes unresolved source
 * certificate identities and ten surviving closed-control masks.
 * The proof bank consists of 3,087 old nonhalting source cylinders,
 * both E/F binary odometers, ten closed-control-mask theorems, and 1,067
 * finite-halt source witnesses. HALT is a distinct physical action.
 *
 * Output is a ranked list of live three-slot (D1,C1,B1) subproblems,
 * NOT a theorem that these branches halt/diverge. Follow up with a
 * Lean Cover for each complement branch.
 */
import assert from "node:assert/strict";
import {readFileSync} from "node:fs";
import {dirname,join} from "node:path";
import {fileURLToPath} from "node:url";
const dir=dirname(fileURLToPath(import.meta.url));
const first=join(dir,"../agent50-raw34-firsthole");
const depth2=JSON.parse(readFileSync(join(first,"depth2-candidate-witnesses.json"),"utf8")).second_level;
const depth3=JSON.parse(readFileSync(join(first,"depth3-candidate-witnesses.json"),"utf8")).witnesses;
assert.equal(depth2.length,74);assert.equal(depth3.length,1206);
const alphabet=["HALT"];
for(const w of "01")for(const d of "LR")for(const q of "ABCDEF")alphabet.push(w+d+q);
assert.equal(alphabet.length,25);
const codeOf=new Map(alphabet.map((a,i)=>[a,i+1])); // code1 HALT; code2 0LA; ...
const slots=[7,5,3,1,8,9,10,11]; // D1 C1 B1 A1 E0 E1 F0 F1
const rootActions=new Map([[0,"1RB"],[2,"1RC"],[4,"0RD"],[6,"1LC"]]);
function parseTable(t){
 const s=t.replaceAll("_","");
 assert.equal(s.length,36,t);
 for(const [i,a] of rootActions)assert.equal(s.slice(i*3,i*3+3),a,t);
 return slots.map(i=>{
  const a=s.slice(i*3,i*3+3);
  assert(a==="---"||codeOf.has(a),a+" in "+t);
  return a==="---"?0:codeOf.get(a);
 });
}
const bank=[];
const add=p=>{assert(p.length===8);bank.push(p);};
"0LA 0LB 0LC 0RA 0RB 0RC 0RD 1LC 1RA 1RB 1RC"
 .split(" ").forEach(a=>add([codeOf.get(a),0,0,0,0,0,0,0]));
depth2.forEach(x=>add(parseTable(x.table)));
add(parseTable("1RB---_1RC---_0RD1LC_1LC1RD_------_------"));
const cd=[];for(const w of "01")for(const d of "LR")for(const q of "CD")cd.push(codeOf.get(w+d+q));
for(const c1 of cd)for(const d1 of cd)add([d1,c1,0,0,0,0,0,0]);
depth3.forEach(x=>add(parseTable(x.table)));
const bcd=[];for(const w of "01")for(const d of "LR")for(const q of "BCD")bcd.push(codeOf.get(w+d+q));
for(const b1 of bcd)for(const c1 of bcd)for(const d1 of bcd)add([d1,c1,b1,0,0,0,0,0]);
for(const t of [
 "1RB1LD_1RC---_0RD0RA_1LC1RD_------_------",
 "1RB---_1RC---_0RD0RE_1LC1RD_---1LD_------",
 "1RB---_1RC---_0RD0LD_1LC0RE_1RD---_------"
])add(parseTable(t));
assert.equal(bank.length,3087);
const oldCount=bank.length;
const counters=[
 "1RB---_1RC---_0RD0LC_1LC1RE_1RD---_------",
 "1RB---_1RC---_0RD0LC_1LC1RF_------_1RD---"
].map(parseTable);
counters.forEach(add);
const withECycles=process.argv.includes("--include-e-cycles");
const withDepth4=process.argv.includes("--include-f-depth4")||withECycles;
const withCycles=process.argv.includes("--include-f-cycles")||withDepth4;
const withEOnly=process.argv.includes("--include-e-ray")||withCycles;
const withLeft=process.argv.includes("--include-f-left")||withCycles;
const withRay=process.argv.includes("--include-f-ray")||withLeft;
const fDirIndex=process.argv.indexOf("--f-depth3-dir");
const fDepth3Dir=fDirIndex<0?"/tmp/a40-raw34-f-cycleunion":process.argv[fDirIndex+1];
const f4DirIndex=process.argv.indexOf("--f-depth4-dir");
const fDepth4Dir=f4DirIndex<0?"/tmp/a40-raw34-f-depth4union":process.argv[f4DirIndex+1];
const eDirIndex=process.argv.indexOf("--e-cycles-dir");
const eCyclesDir=eDirIndex<0?"/tmp/a40-raw34-eunion":process.argv[eDirIndex+1];
function parseSourceRay(file){
 const text=readFileSync(join(dir,file),"utf8");
 const arr=[...text.matchAll(/^\s*\[([\d,\s]+)\],?$/gm)].map(m=>
   m[1].split(",").map(x=>Number(x.trim())));
 for(const p of arr){
   assert.equal(p.length,12);
   for(const [i,a] of rootActions)assert.equal(p[i],codeOf.get(a));
 }
 return arr.map(p=>slots.map(i=>p[i]));
}
const raySource=withRay?[
 ...parseSourceRay("Raw34FRightRay.lean"),
 ...parseSourceRay("Raw34EFRightRay.lean"),
 ...(withLeft?parseSourceRay("Raw34FLeftRay.lean"):[]),
 ...(withEOnly?parseSourceRay("Raw34ERightRay.lean"):[])
]:[];
if(withRay)assert.equal(raySource.length,(withLeft?44:36)+(withEOnly?4:0));
raySource.forEach(add);
function parseSourceCycles(text){
 const rows=[...text.matchAll(/⟨\[([\d,\s]+)\],/g)].map(m=>
   m[1].split(",").map(x=>Number(x.trim())));
 for(const p of rows){
   assert.equal(p.length,12,"source cycle witness must have 12 physical slots");
   for(const [i,a] of rootActions)assert.equal(p[i],codeOf.get(a));
 }
 return rows.map(p=>slots.map(i=>p[i]));
}
let cycleSource=[];
if(withCycles){
 cycleSource.push(...parseSourceCycles(readFileSync(join(dir,"Raw34FDepth2Cycles.lean"),"utf8")));
 assert.equal(cycleSource.length,34);
 for(let i=0;i<12;i++){
   const name="Raw34FDepth3SideShard"+String(i).padStart(3,"0")+".lean";
   cycleSource.push(...parseSourceCycles(readFileSync(join(fDepth3Dir,name),"utf8")));
 }
 assert.equal(cycleSource.length,626,"34 two-slot and 592 source-validated three-slot cycles");
 if(withDepth4){
   for(let i=0;i<93;i++){
     const name="Raw34FDepth4SideShard"+String(i).padStart(3,"0")+".lean";
     cycleSource.push(...parseSourceCycles(readFileSync(join(fDepth4Dir,name),"utf8")));
   }
   assert.equal(cycleSource.length,9857,"34+592+9231 source candidates");
 }
 cycleSource.forEach(add);
}
let eCycleSource=[];
if(withECycles){
 eCycleSource.push(...parseSourceCycles(readFileSync(join(eCyclesDir,"Raw34EDepth2Cycles.lean"),"utf8")));
 for(let i=0;i<12;i++){
   const name="Raw34EDepth3SideShard"+String(i).padStart(3,"0")+".lean";
   eCycleSource.push(...parseSourceCycles(readFileSync(join(eCyclesDir,name),"utf8")));
 }
 for(let i=0;i<93;i++){
   const name="Raw34EDepth4SideShard"+String(i).padStart(3,"0")+".lean";
   eCycleSource.push(...parseSourceCycles(readFileSync(join(eCyclesDir,name),"utf8")));
 }
 assert.equal(eCycleSource.length,9857,"all 9857 E/F-permuted source-cycle tables");
 eCycleSource.forEach(add);
}
const counterCount=counters.length+raySource.length+cycleSource.length+eCycleSource.length;
function loadHalters(file){
 const s=readFileSync(join(dir,file),"utf8");
 const arr=[...s.matchAll(/⟨\[([\d,\s]+)\], \.halt (\d+)⟩/g)]
   .map(m=>({p:m[1].split(",").map(x=>Number(x.trim())),time:Number(m[2])}));
 for(const x of arr){
   assert.equal(x.p.length,12);
   for(const [i,a] of rootActions)assert.equal(x.p[i],codeOf.get(a));
   assert(x.p[7]!==codeOf.get("1RD")&&x.p[7]!==0);
   add(slots.map(i=>x.p[i]));
 }
 return arr.length;
}
const n8=loadHalters("Raw34OtherD1Halt8.lean");
const n9=loadHalters("Raw34OtherD1Halt9New.lean");
assert.equal(n8,109);assert.equal(n9,958);
assert.equal(bank.length,4156+raySource.length);

const stateSlots=["D","C","B","A","E","E","F","F"];
const maskNames=["CDE","CDF","CDEF","BCDE","BCDF","BCDEF",
  "ABCD","ABCDE","ABCDF","ABCDEF"];
const families=maskNames.map((S,i)=>({
  S,bit:1<<i,where:stateSlots.map((state,j)=>S.includes(state)?j:-1).filter(j=>j>=0)
}));
const maskAll=(1<<families.length)-1;
function nextMask(mask,at,code){
 if(mask===0)return 0;
 const action=alphabet[code-1];
 for(const f of families){
  if(mask&f.bit&&f.where.includes(at)&&
      (action==="HALT"||!f.S.includes(action[2])))mask&=~f.bit;
 }
 return mask;
}
function overlap(a,b){return a.every((v,i)=>v===0||b[i]===0||v===b[i]);}
function feasibleGraph(p,f){
 return f.where.every(i=>{
  const c=p[i];if(!c)return true;
  const a=alphabet[c-1];
  return a!=="HALT"&&f.S.includes(a[2]);
 });
}
// Important global consistency check: a genuine short halter cannot share a
// physical completion with a source-proved forever-live certificate.
for(let i=oldCount+counterCount;i<bank.length;i++){
 for(let j=0;j<oldCount+counterCount;j++)
   assert(!overlap(bank[i],bank[j]),"halt/nonhalt cylinder overlap: "+i+" vs "+j);
 for(const f of families)
   assert(!feasibleGraph(bank[i],f),"halt/closed-graph overlap: "+i+" "+f.S);
}
const pow=Array.from({length:9},(_,i)=>25n**BigInt(i));
const memo=new Map();
let memoNodes=0;
function count(ids,at,mask){
 if(ids.some(id=>bank[id].slice(at).every(v=>v===0)))return 0n;
 if(at===8)return mask?0n:1n;
 if(ids.length===0&&mask===0)return pow[8-at];
 const key=at+"|"+mask+"|"+ids.join(",");
 if(memo.has(key))return memo.get(key);
 const wildcard=[],by=Array.from({length:26},()=>[]);
 for(const id of ids){
  const c=bank[id][at];if(c===0)wildcard.push(id);else by[c].push(id);
 }
 let sum=0n;
 for(let c=1;c<=25;c++){
  const next=wildcard.concat(by[c]);
  sum+=count(next,at+1,nextMask(mask,at,c));
 }
 memo.set(key,sum);
 memoNodes++;
 return sum;
}
const idsAll=bank.map((_,i)=>i);
function branch(ids,at,code){
 return {
  ids:ids.filter(i=>bank[i][at]===0||bank[i][at]===code),
  mask:null
 };
}
const totalByD1=[],top=[];
let grand=0n,peak=0n;
for(let d=1;d<=25;d++){
 if(alphabet[d-1]==="1RD")continue;
 const m1=nextMask(maskAll,0,d);
 const id1=branch(idsAll,0,d).ids;
 const mass=count(id1,1,m1);
 totalByD1.push({D1:alphabet[d-1],unclassified:String(mass)});
 grand+=mass;
 for(let c=1;c<=25;c++){
  const id2=branch(id1,1,c).ids,m2=nextMask(m1,1,c);
  for(let b=1;b<=25;b++){
   const id3=branch(id2,2,b).ids,m3=nextMask(m2,2,b);
   const n=count(id3,3,m3);
   if(n>0n){
    top.push({D1:alphabet[d-1],C1:alphabet[c-1],B1:alphabet[b-1],
      residual:String(n),residualPercentOf25power5:Number(n*10000n/pow[5])/100});
    if(n>peak)peak=n;
   }
  }
 }
}
if(!withRay)assert.equal(grand,5471912359n,
 "Raw34 non-D1 residual does not match independent source union subtraction");
if(withRay)assert(grand<5471912359n,"new F-ray sources did not reduce complement");
totalByD1.sort((a,b)=>BigInt(a.unclassified)>BigInt(b.unclassified)?-1:
  BigInt(a.unclassified)<BigInt(b.unclassified)?1:0);
top.sort((a,b)=>BigInt(a.residual)>BigInt(b.residual)?-1:
  BigInt(a.residual)<BigInt(b.residual)?1:0);
console.log(JSON.stringify({
  status:"Exact source-bank 25-way complement rank; branches are OPEN hypotheses",
  root:"1RB---_1RC---_0RD---_1LC---_------_------",
  actionCount:25,oldNonhaltPatterns:oldCount,binaryOdometerPatterns:counters.length,
  rayPatterns:raySource.length,cyclePatterns:cycleSource.length,
  eConjugateCyclePatterns:eCycleSource.length,
  rayNewPhysicalGain:withRay&&!withCycles?String(5471912359n-grand):"0",
  rayAndCycleNewPhysicalGain:withCycles?String(5471912359n-grand):"0",
  additionalCycleGainOverAll44Rays:"Subtract --include-f-left residual externally for exact fresh mass",
  depth4CyclesIncluded:withDepth4,
  earlyHaltPatterns:n8,lateHaltPatterns:n9,graphMasks:maskNames,
  fixedD1:"except 1RD",expectedRemainingD1_1RD:"110397542",
  totalResidualD1not1RD:String(grand),
  plusAgent23Residual:String(grand+110397542n),
  nonzeroThreeSlotPrefixes:top.length,
  bestThreeSlotResidual:String(peak),
  memoizedCountStates:memoNodes,
  D1Distribution:totalByD1,
  topThreeSlotPrefixes:top.slice(0,45)
},null,2));
