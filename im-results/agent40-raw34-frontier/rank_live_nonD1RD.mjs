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
const withMissingThird=process.argv.includes("--include-missing-ef-third");
const withFGrowth=process.argv.includes("--include-f-growth");
const withFDepth5=process.argv.includes("--include-f-depth5");
const withEDepth5=process.argv.includes("--include-e-depth5");
const withExtendedLong=process.argv.includes("--include-extended-long");
const withDepth6Tranche=process.argv.includes("--include-depth6-tranche");
const withDepth6Halts=process.argv.includes("--include-depth6-halts");
const withLateHalts=process.argv.includes("--include-late-halts");
const withEFLeft=process.argv.includes("--include-ef-left-ray");
const withELeft=process.argv.includes("--include-e-left-ray")||withEFLeft;
const withDepth4=process.argv.includes("--include-f-depth4")||withECycles||
  withFDepth5||withEDepth5;
const withCycles=process.argv.includes("--include-f-cycles")||withDepth4;
const withEOnly=process.argv.includes("--include-e-ray")||withCycles||withELeft;
const withLeft=process.argv.includes("--include-f-left")||withCycles||withELeft;
const withRay=process.argv.includes("--include-f-ray")||withLeft;
const fDirIndex=process.argv.indexOf("--f-depth3-dir");
const fDepth3Dir=fDirIndex<0?"/tmp/a40-raw34-f-cycleunion":process.argv[fDirIndex+1];
const f4DirIndex=process.argv.indexOf("--f-depth4-dir");
const fDepth4Dir=f4DirIndex<0?"/tmp/a40-raw34-f-depth4union":process.argv[f4DirIndex+1];
const eDirIndex=process.argv.indexOf("--e-cycles-dir");
const eCyclesDir=eDirIndex<0?"/tmp/a40-raw34-eunion":process.argv[eDirIndex+1];
const efLeftIndex=process.argv.indexOf("--ef-left-dir");
const efLeftDir=efLeftIndex<0?"/tmp/a40-raw34-ef-leftunion":process.argv[efLeftIndex+1];
const missingThirdIndex=process.argv.indexOf("--missing-third-dir");
const missingThirdDir=missingThirdIndex<0?"/tmp/a40-raw34-missing-thirdunion":process.argv[missingThirdIndex+1];
const f5DirIndex=process.argv.indexOf("--f-depth5-dir");
const fDepth5Dir=f5DirIndex<0?"/tmp/a50-raw34-f-depth5":process.argv[f5DirIndex+1];
const e5DirIndex=process.argv.indexOf("--e-depth5-dir");
const eDepth5Dir=e5DirIndex<0?"/tmp/a50-raw34-e-depth5":process.argv[e5DirIndex+1];
const halt5DirIndex=process.argv.indexOf("--halt-depth5-dir");
const haltDepth5Dir=halt5DirIndex<0?"/tmp/a40-raw34-depth5-full":process.argv[halt5DirIndex+1];
const extendedDirIndex=process.argv.indexOf("--extended-long-dir");
const extendedLongDir=extendedDirIndex<0?"/tmp/a50-raw34-extended-long":process.argv[extendedDirIndex+1];
const depth6DirIndex=process.argv.indexOf("--depth6-dir");
const depth6Dir=depth6DirIndex<0?"/tmp/a50-raw34-depth6":process.argv[depth6DirIndex+1];
const depth6HaltDirIndex=process.argv.indexOf("--depth6-halt-dir");
const depth6HaltDir=depth6HaltDirIndex<0?"/tmp/a50-raw34-depth6-halts":process.argv[depth6HaltDirIndex+1];
function parseSourceRay(file){
 const text=readFileSync(file.startsWith("/")?file:join(dir,file),"utf8");
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
 ...(withEOnly?parseSourceRay("Raw34ERightRay.lean"):[]),
 ...(withELeft?parseSourceRay("Raw34ELeftRay.lean"):[]),
 ...(withEFLeft?Array.from({length:16},(_,i)=>
   parseSourceRay(join(efLeftDir,"Raw34EFLeftShard"+String(i).padStart(3,"0")+".lean"))).flat():[])
]:[];
if(withRay)assert.equal(raySource.length,
  (withLeft?44:36)+(withEOnly?4:0)+(withELeft?8:0)+(withEFLeft?1024:0));
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
let fDepth5Source=[];
if(withFDepth5){
 const m=JSON.parse(readFileSync(join(fDepth5Dir,"manifest.json"),"utf8"));
 assert(Number.isInteger(m.selectedCount)&&m.selectedCount>0);
 for(const unit of m.modules)
   fDepth5Source.push(...parseSourceCycles(
     readFileSync(join(fDepth5Dir,unit.module+".lean"),"utf8")));
 assert.equal(fDepth5Source.length,m.selectedCount);
 fDepth5Source.forEach(add);
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
let eDepth5Source=[];
if(withEDepth5){
 const m=JSON.parse(readFileSync(join(eDepth5Dir,"manifest.json"),"utf8"));
 assert(Number.isInteger(m.count)&&m.count>0);
 for(const unit of m.modules)
   eDepth5Source.push(...parseSourceCycles(
     readFileSync(join(eDepth5Dir,unit.module+".lean"),"utf8")));
 assert.equal(eDepth5Source.length,m.count);
 eDepth5Source.forEach(add);
}
let extendedLongSource=[];
if(withExtendedLong){
 const m=JSON.parse(readFileSync(join(extendedLongDir,"manifest.json"),"utf8"));
 assert.equal(m.fCount,481);assert.equal(m.eCount,481);
 for(const unit of m.modules)
   extendedLongSource.push(...parseSourceCycles(
     readFileSync(join(extendedLongDir,unit.module+".lean"),"utf8")));
 assert.equal(extendedLongSource.length,962);
 extendedLongSource.forEach(add);
}
let depth6Source=[];
if(withDepth6Tranche){
 const m=JSON.parse(readFileSync(join(depth6Dir,"manifest.json"),"utf8"));
 assert.equal(m.limit,100000);
 for(const unit of [...m.fModules,...m.eModules])
   depth6Source.push(...parseSourceCycles(
     readFileSync(join(depth6Dir,unit.module+".lean"),"utf8")));
 assert.equal(depth6Source.length,200000);
 depth6Source.forEach(add);
}
let missingThirdSource=[];
if(withMissingThird){
 for(let i=0;i<4;i++){
   const name="Raw34MissingEFThirdShard"+String(i).padStart(3,"0")+".lean";
   missingThirdSource.push(...parseSourceCycles(readFileSync(join(missingThirdDir,name),"utf8")));
 }
 assert.equal(missingThirdSource.length,168,"168 omitted physical source-symmetry witnesses");
 missingThirdSource.forEach(add);
}
const fGrowthSource=withFGrowth?[
  "1RB---_1RC---_0RD0RF_1LC1RD_------_---1LD",
  "1RB---_1RC---_0RD0LD_1LC0RF_------_1RD---"
].map(parseTable):[];
fGrowthSource.forEach(add);
const counterCount=counters.length+raySource.length+cycleSource.length+
  fDepth5Source.length+eCycleSource.length+eDepth5Source.length+
  extendedLongSource.length+depth6Source.length+
  missingThirdSource.length+fGrowthSource.length;
function loadHalters(file){
 const s=readFileSync(file.startsWith("/")?file:join(dir,file),"utf8");
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
let nDepth6Halts=0;
if(withDepth6Halts){
 const m=JSON.parse(readFileSync(join(depth6HaltDir,"manifest.json"),"utf8"));
 assert.equal(m.selectedCount,138017);
 const parseDirect=file=>{
   const text=readFileSync(join(depth6HaltDir,file),"utf8");
   return [...text.matchAll(/⟨\[([\d,\s]+)\],\s*(\d+)⟩/g)]
     .map(mm=>mm[1].split(",").map(x=>Number(x.trim())));
 };
 for(const unit of [...m.fModules,...m.eModules]){
   const arr=parseDirect(unit.module+".lean");
   assert.equal(arr.length,unit.size);
   for(const p of arr){
     assert.equal(p.length,12);
     for(const [i,a] of rootActions)assert.equal(p[i],codeOf.get(a));
     add(slots.map(i=>p[i]));
   }
   nDepth6Halts+=arr.length;
 }
 assert.equal(nDepth6Halts,276034);
}
let nAdditionalLate=0;
if(withLateHalts){
 nAdditionalLate+=loadHalters("Raw34LateThreeSlotHalters.lean");
 for(let i=0;i<5;i++)
   nAdditionalLate+=loadHalters("Raw34Depth4HalterShard"+String(i).padStart(2,"0")+".lean");
 const m=JSON.parse(readFileSync(join(haltDepth5Dir,"manifest.json"),"utf8"));
 assert.equal(m.numSourceCylinders,13884);
 for(const unit of m.sourceTheorems)
   nAdditionalLate+=loadHalters(join(haltDepth5Dir,unit.module+".lean"));
 assert.equal(nAdditionalLate,14424,"5+535+13,884 accepted late halter cylinders");
}
assert.equal(bank.length,4156+raySource.length+cycleSource.length+
  fDepth5Source.length+eCycleSource.length+eDepth5Source.length+
  extendedLongSource.length+depth6Source.length+
  missingThirdSource.length+fGrowthSource.length+nDepth6Halts+nAdditionalLate);

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
// Compile all source cylinders and the ten closed-control families into a
// reduced ordered 25-way decision diagram. This avoids decimal-ID-list memo
// keys, whose duplication exceeded the runner heap after depth-five banks.
const haltStart=oldCount+counterCount;
const pow=Array.from({length:9},(_,i)=>25n**BigInt(i));
const nodes=[{at:8,ch:null},{at:8,ch:null}];
const unique=Array.from({length:8},()=>new Map());
function mk(at,ch){
 let same=true;
 for(let i=1;i<25;i++)if(ch[i]!==ch[0]){same=false;break;}
 if(same)return ch[0];
 const key=ch.join(","),hit=unique[at].get(key);
 if(hit!==undefined)return hit;
 const id=nodes.length;nodes.push({at,ch:ch.slice()});unique[at].set(key,id);return id;
}
function apply2(a,b,isAnd,memo){
 if(isAnd){if(a===0||b===0)return 0;if(a===1)return b;if(b===1)return a;}
 else {if(a===1||b===1)return 1;if(a===0)return b;if(b===0)return a;}
 if(a===b)return a;
 const lo=Math.min(a,b),hi=Math.max(a,b),key=lo+","+hi,old=memo.get(key);
 if(old!==undefined)return old;
 const va=nodes[a].at,vb=nodes[b].at,at=Math.min(va,vb),ch=Array(25);
 for(let c=0;c<25;c++){
  const x=va===at?nodes[a].ch[c]:a,y=vb===at?nodes[b].ch[c]:b;
  ch[c]=apply2(x,y,isAnd,memo);
 }
 const out=mk(at,ch);memo.set(key,out);return out;
}
const union=(a,b)=>apply2(a,b,false,new Map());
const intersect=(a,b)=>apply2(a,b,true,new Map());
function cubeBDD(p){
 let r=1;
 for(let at=7;at>=0;at--){const code=p[at];if(!code)continue;
  const ch=Array(25).fill(0);ch[code-1]=r;r=mk(at,ch);}
 return r;
}
function familyBDD(f){
 let r=1;const where=new Set(f.where);
 for(let at=7;at>=0;at--){if(!where.has(at))continue;
  const ch=Array(25).fill(0);
  for(let c=1;c<=25;c++){const a=alphabet[c-1];
   if(a!=="HALT"&&f.S.includes(a[2]))ch[c-1]=r;}
  r=mk(at,ch);
 }
 return r;
}
function compileCubes(ps,at=0){
 if(ps.length===0)return 0;
 if(at===8)return 1;
 const wild=[],by=Array.from({length:26},()=>[]);
 for(const p of ps){const c=p[at];if(c===0)wild.push(p);else by[c].push(p);}
 const w=compileCubes(wild,at+1);
 if(w===1)return 1;
 const ch=Array(25);
 for(let c=1;c<=25;c++)ch[c-1]=union(w,compileCubes(by[c],at+1));
 return mk(at,ch);
}
let nonhaltRoot=compileCubes(bank.slice(0,haltStart));
for(const f of families)nonhaltRoot=union(nonhaltRoot,familyBDD(f));
const haltRoot=compileCubes(bank.slice(haltStart));
assert.equal(intersect(nonhaltRoot,haltRoot),0,"halting/nonhalting proof-bank overlap");
const coverageRoot=union(nonhaltRoot,haltRoot),countMemo=new Map();
function coveredCount(id,at){
 if(id===0)return 0n;if(id===1)return pow[8-at];
 const n=nodes[id];assert(n.at>=at);
 let base=countMemo.get(id);
 if(base===undefined){base=0n;for(const child of n.ch)base+=coveredCount(child,n.at+1);countMemo.set(id,base);}
 return pow[n.at-at]*base;
}
function restrictAt(id,at,code){
 if(id<=1)return id;const n=nodes[id];assert(n.at>=at);
 return n.at===at?n.ch[code-1]:id;
}
const totalByD1=[],top=[];
let grand=0n,peak=0n;
for(let d=1;d<=25;d++){
 if(alphabet[d-1]==="1RD")continue;
 const id1=restrictAt(coverageRoot,0,d);
 const mass=pow[7]-coveredCount(id1,1);
 totalByD1.push({D1:alphabet[d-1],unclassified:String(mass)});
 grand+=mass;
 for(let c=1;c<=25;c++){
  const id2=restrictAt(id1,1,c);
  for(let b=1;b<=25;b++){
   const id3=restrictAt(id2,2,b);
   const n=pow[5]-coveredCount(id3,3);
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
  fDepth5CyclePatterns:fDepth5Source.length,
  eConjugateCyclePatterns:eCycleSource.length,
  eDepth5CyclePatterns:eDepth5Source.length,
  extendedLongCyclePatterns:extendedLongSource.length,
  depth6CyclePatterns:depth6Source.length,
  missingNonEFConjugateThirdPatterns:missingThirdSource.length,
  fConjugateUnboundedGrowthPatterns:fGrowthSource.length,
  rayNewPhysicalGain:withRay&&!withCycles?String(5471912359n-grand):"0",
  rayAndCycleNewPhysicalGain:withCycles?String(5471912359n-grand):"0",
  additionalCycleGainOverAll44Rays:"Subtract --include-f-left residual externally for exact fresh mass",
  depth4CyclesIncluded:withDepth4,
  earlyHaltPatterns:n8,lateHaltPatterns:n9,
  additionalLateHaltPatterns:nAdditionalLate,
  depth6DirectHaltPatterns:nDepth6Halts,graphMasks:maskNames,
  fixedD1:"except 1RD",expectedRemainingD1_1RD:"110397542",
  totalResidualD1not1RD:String(grand),
  plusAgent23Residual:String(grand+110397542n),
  nonzeroThreeSlotPrefixes:top.length,
  bestThreeSlotResidual:String(peak),
  memoizedCountStates:nodes.length,mddNodes:nodes.length,
  D1Distribution:totalByD1,
  topThreeSlotPrefixes:top.slice(0,45)
},null,2));
