#!/usr/bin/env node
/**
 * Source-producing *new* first-query 4-fixed-slot F-branch sidecycles.
 * 34 D1/F0 cycles are excluded at depth two. 592 next-source cycles are
 * excluded at depth three. Of 894 remaining depth-three source cubes
 * with genuinely undefined first queried instruction, resolving each
 * next source instruction in 25 physical ways gives 9,231 additional
 * shifted-half-tape recurrence certificates.
 *
 * Run the original-source Lean finite side-cycle checker on all generated
 * witnesses before claiming their infinite-run conclusions. The finite
 * enumerator is not itself a proof of nonhalting.
 */
import assert from "node:assert/strict";
import {mkdirSync,writeFileSync} from "node:fs";
import {join} from "node:path";
const args=process.argv.slice(2);
function opt(name,def){const i=args.indexOf(name);return i<0?def:args[i+1];}
const out=opt("--output","/tmp/raw34-f-depth4-cycles");
const shardSize=Number(opt("--shard-size","100"));
assert(Number.isInteger(shardSize)&&shardSize>0);
mkdirSync(out,{recursive:true});
const alphabet=["HALT"];
for(const w of "01")for(const d of "LR")for(const q of "ABCDEF")
  alphabet.push(w+d+q);
const root=[21,0,22,0,11,0,16,0,0,0,0,0];
const dCodes=["0LF","1LF","0RF","1RF"].map(x=>alphabet.indexOf(x)+1);
function trace(p,cap=100){
 let s=0,h=0,ones=new Set(),hist=[];
 for(let t=0;t<=cap;t++){
  hist.push({s,h,ones:new Set(ones)});
  const sl=2*s+(ones.has(h)?1:0),action=p[sl];
  if(action===0||action===1)return {
    kind:action===0?"unknown":"halt",slot:sl,hist,t
  };
  const v=action-2;
  v>=12?ones.add(h):ones.delete(h);
  s=v%6;h+=v%12>=6?1:-1;
 }
 return {kind:"long",hist};
}
function sideWitness(hist){
 const max=Math.min(hist.length,60);
 for(let entry=0;entry<max;entry++)
 for(let j=entry+1;j<Math.min(hist.length,entry+31);j++){
  const a=hist[entry],b=hist[j],delta=b.h-a.h;
  if(a.s!==b.s)continue;
  for(const right of [true,false]){
   if(right?delta<0:delta>0)continue;
   let boundary=right?Infinity:-Infinity;
   for(let t=entry;t<j;t++){
    boundary=right?Math.min(boundary,hist[t].h)
                  :Math.max(boundary,hist[t].h);
   }
   if([...a.ones].some(x=>(right?x>=boundary:x<=boundary)&&
       !b.ones.has(x+delta)))continue;
   if([...b.ones].some(y=>(right?y-delta>=boundary:y-delta<=boundary)&&
       !a.ones.has(y-delta)))continue;
   return {entry,period:j-entry,right,boundary};
  }
 }
 return null;
}
const earlier=[],bank=[],byD={},summary={old2:0,open2:0,old3:0,open3:0,
children:0,halt:0,stillOpen:0,longBy100:0};
for(const d of dCodes){
 let added=0;
 for(let f=1;f<=25;f++){
  const p=root.slice();p[7]=d;p[10]=f;
  const first=trace(p),w2=sideWitness(first.hist);
  if(w2){summary.old2++;earlier.push(p.slice());continue;}
  if(first.kind!=="unknown")continue;
  summary.open2++;
  for(let a=1;a<=25;a++){
   p[first.slot]=a;
   const second=trace(p),w3=sideWitness(second.hist);
   if(w3){
    summary.old3++;earlier.push(p.slice());p[first.slot]=0;continue;
   }
   if(second.kind!=="unknown"){p[first.slot]=0;continue;}
   summary.open3++;
   for(let x=1;x<=25;x++){
    p[second.slot]=x;summary.children++;
    const third=trace(p),w4=sideWitness(third.hist);
    if(w4){bank.push({codes:p.slice(),...w4});added++;}
    else if(third.kind==="halt")summary.halt++;
    else if(third.kind==="unknown")summary.stillOpen++;
    else summary.longBy100++;
    p[second.slot]=0;
   }
   p[first.slot]=0;
  }
 }
 byD[alphabet[d-1]]=added;
}
assert.deepEqual(summary,{
 old2:34,open2:62,old3:592,open3:894,children:22350,
 halt:894,stillOpen:12156,longBy100:69
});
assert.equal(bank.length,9231);
assert.equal(new Set(bank.map(x=>x.codes.join(","))).size,bank.length);
assert.equal(bank.every(w=>w.codes.filter((x,i)=>x!==0&&![0,2,4,6].includes(i)).length===4),true);
const conflict=(a,b)=>a.some((x,i)=>x!==0&&b[i]!==0&&x!==b[i]);
let comparisons=0;
for(let i=0;i<bank.length;i++){
 for(let j=i+1;j<bank.length;j++){
  comparisons++;
  assert(conflict(bank[i].codes,bank[j].codes),
    `new all-time sidecycles overlap ${i}:${j}`);
 }
 for(const prior of earlier){
  comparisons++;
  assert(conflict(bank[i].codes,prior),
    `new all-time sidecycle overlaps accepted-prior candidate ${i}`);
 }
}
const modules=[];
for(let i=0;i<Math.ceil(bank.length/shardSize);i++){
 const entries=bank.slice(i*shardSize,(i+1)*shardSize),
  suffix=String(i).padStart(3,"0"),
  module=`Raw34FDepth4SideShard${suffix}`,
  namespace=`BB6.Agent40FDepth4.${module}`;
 modules.push({module,namespace,size:entries.length});
 const source=`import Raw34D1RDOneStepCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-! Generated genuine half-line recurrence proofs, fixed D1, F0, and two
other first-queried instructions. Everything else may include HALT. -/
namespace ${namespace}
open BB6Coverage BB6.Agent23Raw34Next BB6Coverage.Agent50SideCycle
structure CycleWitness where
  codes : List Nat
  entry : Nat
  period : Nat
  right : Bool
  boundary : Int
def witnesses : List CycleWitness := [
${entries.map(x=>`  ⟨[${x.codes.join(",")}], ${x.entry}, ${x.period}, ${x.right}, ${x.boundary}⟩`).join(",\n")}
]
def checkCycle (w : CycleWitness) : Bool :=
  decide (0 < w.period) &&
    fastSideCycleCheck (table w.codes) w.entry w.period w.right w.boundary
theorem count : witnesses.length = ${entries.length} := by decide
theorem checked : witnesses.all checkCycle = true := by decide +kernel
theorem all_never (w : CycleWitness) (hw : w ∈ witnesses)
    (m : Machine) (hm : compatible (table w.codes) m) :
    NeverHalts m := by
  have hh : checkCycle w = true := List.all_eq_true.mp checked w hw
  obtain ⟨hpos,hc⟩ : decide (0 < w.period) = true ∧
      fastSideCycleCheck (table w.codes)
        w.entry w.period w.right w.boundary = true := by
    simpa only [checkCycle, Bool.and_eq_true] using hh
  exact fastSideCycleCheck_sound (table w.codes)
    w.entry w.period w.right w.boundary
    (of_decide_eq_true hpos) hc m hm
#print axioms count
#print axioms checked
#print axioms all_never
end ${namespace}
`;
 writeFileSync(join(out,module+".lean"),source);
}
const volume=BigInt(bank.length)*25n**4n;
assert.equal(volume,3605859375n);
const report={status:"Source-generatable 4-fixed-slot half-line cycles (require Lean acceptance)",
 root:"1RB---_1RC---_0RD---_1LC---_------_------",
 depths:summary,byD,sourceCylinders:bank.length,physicalMassGross:String(volume),
 exactPairwiseDisjointnessComparisons:comparisons,
 modules,shardSize};
writeFileSync(join(out,"manifest.json"),JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify({...report,modules:modules.map(x=>x.namespace+".all_never")},null,2));
