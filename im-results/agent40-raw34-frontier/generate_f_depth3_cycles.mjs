#!/usr/bin/env node
/**
 * Discover and export all early source-verifiable F-branch depth-3
 * translated-half-line cycles outside depth-2 cycles.  Assumptions:
 *   fixed genuine Raw34 four transitions;
 *   D1 ∈ {0LF,1LF,0RF,1RF};
 *   first queried F0 is fixed; then fix the first genuinely unknown
 *   instruction read by that partial run.
 *
 * This script is ONLY an enumerator and candidate producer. Every claimed
 * never-halting theorem is checked by original Lean fastSideCycleCheck and
 * fastSideCycleCheck_sound in the generated modules.
 */
import assert from "node:assert/strict";
import {mkdirSync,writeFileSync} from "node:fs";
import {join} from "node:path";
const args=process.argv.slice(2);
function opt(name,otherwise){const i=args.indexOf(name);return i<0?otherwise:args[i+1];}
const out=opt("--output","/tmp/raw34-f-depth3-cycles"),
      shardSize=Number(opt("--shard-size","50"));
assert(shardSize>0&&Number.isInteger(shardSize));
mkdirSync(out,{recursive:true});
const actions=["HALT"];
for(const w of "01")for(const d of "LR")for(const q of "ABCDEF")
 actions.push(w+d+q);
const root=[21,0,22,0,11,0,16,0,0,0,0,0],
      dCodes=["0LF","1LF","0RF","1RF"].map(x=>actions.indexOf(x)+1);
function simulate(p,max=84){
 let q=0,h=0,ones=new Set(),hist=[];
 for(let t=0;t<=max;t++){
  hist.push({q,h,ones:new Set(ones)});
  const sl=2*q+(ones.has(h)?1:0),a=p[sl];
  if(a===0||a===1)return {hist,kind:a===0?"unknown":"halt",slot:sl};
  const x=a-2;
  x>=12?ones.add(h):ones.delete(h);
  q=x%6;h+=x%12>=6?1:-1;
 }
 return {hist,kind:"long"};
}
function witness(hist){
 for(let e=0;e<Math.min(60,hist.length);e++)
 for(let j=e+1;j<Math.min(hist.length,e+31);j++){
  const a=hist[e],b=hist[j],delta=b.h-a.h;
  if(a.q!==b.q)continue;
  for(const right of [true,false]){
   if(right?delta<0:delta>0)continue;
   let boundary=right?Infinity:-Infinity;
   for(let t=e;t<j;t++)
    boundary=right?Math.min(boundary,hist[t].h):
                   Math.max(boundary,hist[t].h);
   if([...a.ones].some(x=>(right?x>=boundary:x<=boundary)&&
       !b.ones.has(x+delta)))continue;
   if([...b.ones].some(y=>(right?y-delta>=boundary:y-delta<=boundary)&&
       !a.ones.has(y-delta)))continue;
   return {entry:e,period:j-e,right,boundary};
  }
 }
 return null;
}
const bank=[],byD={},stats={parents:0,oldCycles:0,trials:0,halters:0,unknown:0};
for(const d of dCodes)for(let f=1;f<=25;f++){
 const p=root.slice();p[7]=d;p[10]=f;
 const initial=simulate(p),old=witness(initial.hist);
 if(old){stats.oldCycles++;continue;}
 if(initial.kind!=="unknown")continue;
 stats.parents++;
 for(let x=1;x<=25;x++){
  p[initial.slot]=x;stats.trials++;
  const s=simulate(p),w=witness(s.hist);
  if(w){
   bank.push({codes:p.slice(),...w});
   const name=actions[d-1];
   byD[name]=(byD[name]||0)+1;
  }else if(s.kind==="halt")stats.halters++;
  else if(s.kind==="unknown")stats.unknown++;
  p[initial.slot]=0;
 }
}
assert.equal(stats.oldCycles,34);
assert.equal(stats.parents,62);
assert.equal(stats.trials,1550);
assert.equal(bank.length,592);
assert.equal(new Set(bank.map(x=>x.codes.join(","))).size,592);
const conflict=(a,b)=>a.some((x,i)=>x!==0&&b[i]!==0&&x!==b[i]);
for(let i=0;i<bank.length;i++)for(let j=i+1;j<bank.length;j++)
 assert(conflict(bank[i].codes,bank[j].codes),
   `overlap: ${i} and ${j}`);
const modules=[];
for(let i=0;i<Math.ceil(bank.length/shardSize);i++){
 const entries=bank.slice(i*shardSize,(i+1)*shardSize),
   suffix=String(i).padStart(3,"0"),
   module=`Raw34FDepth3SideShard${suffix}`,
   namespace=`BB6.Agent40FDepth3.${module}`;
 modules.push({module,namespace,size:entries.length});
 const lean=`import Raw34D1RDOneStepCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! The source checker establishes an all-time translated half-line cycle
on the genuine blank tape for any completion of each listed partial table.
Generated deterministically by generate_f_depth3_cycles.mjs. -/
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
  have h : decide (0 < w.period) = true &&
      fastSideCycleCheck (table w.codes)
        w.entry w.period w.right w.boundary = true := hh
  obtain ⟨hpos,hc⟩ := Bool.and_eq_true.mp h
  exact fastSideCycleCheck_sound (table w.codes)
    w.entry w.period w.right w.boundary
    (of_decide_eq_true hpos) hc m hm
#print axioms count
#print axioms checked
#print axioms all_never
end ${namespace}
`;
 writeFileSync(join(out,module+".lean"),lean);
}
const mass=BigInt(bank.length)*25n**5n;
assert.equal(mass,5781250000n);
const report={status:"exact candidate generation; source theorem requires Lean CI",
trials:stats.trials,cyclesAlreadyAtDepth2:stats.oldCycles,
firstQueryThirdSlotCycles:bank.length,shards:modules.length,shardSize,
rawPhysicalMass:String(mass),pairwiseDisjoint:true,
byD,stats,modules};
writeFileSync(join(out,"manifest.json"),JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify({...report,modules:modules.map(x=>x.namespace+".all_never")},null,2));
