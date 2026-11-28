#!/usr/bin/env node
/**
 * Genuine Raw34 first-undefined-instruction expansion, then semantic
 * compression to the instructions *actually queried* in each halting run.
 *
 * Source convention: code 0 = unknown, 1 = HALT, 2..25 = ordinary
 * write/turn/state moves. Generates Lean source (not an external oracle):
 * every emitted row is kernel checked through finiteHaltCheck and its
 * original-source soundness proof; no native_decide/sorry. Families are
 * truly disjoint literal physical cylinders, not quotient classes.
 *
 * --max-fixed 4: 1,024 largest (3/4-slot) minimal cylinders = 456,250,000
 * --max-fixed 5: all 13,884 minimal cylinders = 657,187,500.
 */
import assert from "node:assert/strict";
import {readFileSync, writeFileSync, mkdirSync} from "node:fs";
import {dirname,join} from "node:path";
import {fileURLToPath} from "node:url";
const dir=dirname(fileURLToPath(import.meta.url));
const args=process.argv.slice(2);
function opt(name,otherwise){
 const i=args.indexOf(name);return i<0?otherwise:args[i+1];
}
const maxFixed=Number(opt("--max-fixed","4")),shardSize=Number(opt("--shard-size","64"));
const skipDisjointness=args.includes("--skip-disjointness");
const output=opt("--output",join(dir,"generated-depth5"));
assert([4,5].includes(maxFixed));assert(Number.isInteger(shardSize)&&shardSize>0);
mkdirSync(output,{recursive:true});
const root=[21,0,22,0,11,0,16,0,0,0,0,0];
const alphabet=["HALT"];
for(const w of "01")for(const d of "LR")for(const q of "ABCDEF")
 alphabet.push(w+d+q);
const haltOf=new Map(alphabet.map((s,i)=>[s,i+1]));
assert.equal(haltOf.get("1RD"),23);
function trace(p,max=26){
 let q=0,h=0,ones=new Set(),queried=0;
 for(let t=0;t<=max;t++){
  const slot=2*q+(ones.has(h)?1:0),code=p[slot];
  if(code===0)return {kind:0,t,slot,queried};
  queried|=1<<slot;
  if(code===1)return {kind:1,t,queried};
  const x=code-2;
  x>=12?ones.add(h):ones.delete(h);
  q=x%6;h+=x%12>=6?1:-1;
 }
 return {kind:2,queried};
}
const map=new Map(),fixedSlots=[0,2,4,6];
let rawCount=0,distinctTriples=0,depth4Open=0;
for(let d=1;d<=25;d++){
 if(d===haltOf.get("1RD"))continue;
 for(let c=1;c<=25;c++)for(let b=1;b<=25;b++){
  let p=root.slice();p[7]=d;p[5]=c;p[3]=b;
  const first=trace(p);
  if(first.kind!==0)continue;
  distinctTriples++;
  for(let x=1;x<=25;x++){
   p[first.slot]=x;
   const second=trace(p);
   if(second.kind!==0){p[first.slot]=0;continue;}
   depth4Open++;
   for(let y=1;y<=25;y++){
    p[second.slot]=y;
    const third=trace(p);
    if(third.kind===1&&third.t>=9){
     rawCount++;
     const q=p.map((v,i)=>fixedSlots.includes(i)||(third.queried&(1<<i))?v:0);
     const key=q.join(",");
     const prev=map.get(key);
     if(prev)assert.equal(prev.n,third.t);
     else map.set(key,{codes:q,n:third.t});
    }
    p[second.slot]=0;
   }
   p[first.slot]=0;
  }
 }
}
assert.equal(distinctTriples,6353);
assert.equal(depth4Open,80904);
assert.equal(rawCount,42060);
assert.equal(map.size,13884);
const numFixed=w=>w.codes.filter((x,i)=>x!==0&&!fixedSlots.includes(i)).length;
const hist={};for(const w of map.values()){const k=numFixed(w);hist[k]=(hist[k]??0)+1;}
assert.deepEqual(hist,{"3":6,"4":1018,"5":12860});
const selected=[...map.values()].filter(w=>numFixed(w)<=maxFixed);
selected.sort((a,b)=>a.codes.join(",").localeCompare(b.codes.join(","))||a.n-b.n);
assert.equal(selected.length,maxFixed===4?1024:13884);
let volume=0n;for(const w of selected)volume+=25n**BigInt(8-numFixed(w));
assert.equal(volume,maxFixed===4?456250000n:657187500n);
// Every new genuine halter is disjoint from earlier halters because all
// cylinder prefixes determine a unique original blank-run halting time.
// Check literal disjointness as well on the 1,024 large maximal cylinders.
const conflict=(a,b)=>a.some((v,i)=>v&&b[i]&&v!==b[i]);
const parse=file=>[...readFileSync(join(dir,file),"utf8")
  .matchAll(/⟨\[([\d,\s]+)\], \.halt (\d+)⟩/g)]
  .map(m=>m[1].split(",").map(x=>Number(x.trim())));
const previous=[
  ...parse("Raw34OtherD1Halt8.lean"),
  ...parse("Raw34OtherD1Halt9New.lean"),
  ...parse("Raw34LateThreeSlotHalters.lean"),
  ...Array.from({length:5},(_,i)=>parse(`Raw34Depth4HalterShard${String(i).padStart(2,"0")}.lean`)).flat()
];
assert.equal(previous.length,1607); // 109+958+5+535
// Strong literal disjointness, independently of the semantic
// uniqueness-of-first-halt argument: 96,375,786 pair tests for maxFixed 5.
let pairChecks=0,priorChecks=0;
for(let i=0;i<selected.length;i++){
 for(let j=i+1;j<selected.length;j++){
  pairChecks++;
  assert(conflict(selected[i].codes,selected[j].codes),
    `overlapping new minimal cylinders ${i}:${j}`);
 }
 for(const p of previous){
  priorChecks++;
  assert(conflict(selected[i].codes,p),
    `new source overlaps previous genuine halting certificate ${i}`);
 }
}

const shards=Math.ceil(selected.length/shardSize),names=[];
for(let i=0;i<shards;i++){
 const xs=selected.slice(i*shardSize,(i+1)*shardSize);
 const suffix=String(i).padStart(3,"0");
 const module=`Raw34Depth5LargeShard${suffix}`;
 const ns=`BB6.Agent40Depth5.${module}`;
 names.push({module,ns,n:xs.length});
 const source=`import Raw34EarlyHaltersSound
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! This original-source first-query halting certificate bank uses actual
queried cells; all omitted slots are unassigned, including potential HALTs.
The original blank-tape semantics and exact finiteHaltCheck are kernel checked.
Generated by im-results/agent40-raw34-frontier/generate_depth5_halts.mjs. -/
namespace ${ns}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent23Raw34Next BB6.Agent40Raw34EarlyHalters
def witnesses : List Witness := [
${xs.map(w=>`  ⟨[${w.codes.join(",")}], .halt ${w.n}⟩`).join(",\n")}
]
theorem count : witnesses.length = ${xs.length} := by decide
theorem checked : witnesses.all check = true := by decide +kernel
theorem short : witnesses.all (isShortHalt 27) = true := by decide
theorem all_halt (w : Witness) (hw : w ∈ witnesses)
    (m : Machine) (hm : compatible (table w.codes) m) :
    ∃ n : Nat, n+1 ≤ 27 ∧ HaltsAfter m n :=
  short_halt_sound 27 w
    (List.all_eq_true.mp short w hw)
    (List.all_eq_true.mp checked w hw) m hm
theorem all_weighted (w : Witness) (hw : w ∈ witnesses) :
    ∀ m, compatible (table w.codes) m → WeightedBound 32 m :=
  check_sound w (List.all_eq_true.mp checked w hw)
#print axioms count
#print axioms checked
#print axioms short
#print axioms all_halt
#print axioms all_weighted
end ${ns}
`;
 writeFileSync(join(output,module+".lean"),source);
}
const report={status:"source-generated, kernel-checkable genuine halting physical cylinders",
 rawFifthQueryHaltCount:rawCount,distinctMinimalCylinders:map.size,
 numSourceCylinders:selected.length,maxFixed,shardSize,numShards:shards,
 fixedSlotHistogram:hist,physicalCoverageNew:String(volume),
 remainingSourceFrontierAfterAcceptance:String(5324497401n-volume),
 sourceTheorems:names,oldDisjointnessChecked:true,pairwiseChecks:pairChecks,
  earlierSourceComparisons:priorChecks,disjointnessSkipped:skipDisjointness};
writeFileSync(join(output,"manifest.json"),JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify({...report,sourceTheorems:names.map(x=>x.ns+".all_halt")},null,2));
