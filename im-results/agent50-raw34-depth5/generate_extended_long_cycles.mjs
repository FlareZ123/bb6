#!/usr/bin/env node
/**
 * Recover Raw34 F branches that exceeded the original cap/window but admit
 * the same source-proved half-line recurrence with a larger finite search.
 * Generation is untrusted; every emitted witness is rechecked in Lean by
 * fastSideCycleCheck_sound.
 */
import assert from "node:assert/strict";
import {mkdirSync,writeFileSync} from "node:fs";
import {join} from "node:path";
const args=process.argv.slice(2);
function opt(name,def){const i=args.indexOf(name);return i<0?def:args[i+1];}
const output=opt("--output","/tmp/a50-raw34-extended-long");
mkdirSync(output,{recursive:true});
const alphabet=["HALT"];
for(const w of "01")for(const d of "LR")for(const q of "ABCDEF")alphabet.push(w+d+q);
const root=[21,0,22,0,11,0,16,0,0,0,0,0];
const dCodes=["0LF","1LF","0RF","1RF"].map(x=>alphabet.indexOf(x)+1);
function trace(p,cap=100){
 let q=0,h=0,ones=new Set(),hist=[];
 for(let t=0;t<=cap;t++){
  hist.push({q,h,ones:new Set(ones)});
  const slot=2*q+(ones.has(h)?1:0),action=p[slot];
  if(action===0||action===1)return {kind:action===0?"unknown":"halt",slot,hist,t};
  const v=action-2;v>=12?ones.add(h):ones.delete(h);q=v%6;h+=v%12>=6?1:-1;
 }
 return {kind:"long",hist};
}
function sideWitness(hist,maxEntry=60,maxPeriod=30){
 const max=Math.min(hist.length,maxEntry);
 for(let entry=0;entry<max;entry++)
 for(let j=entry+1;j<Math.min(hist.length,entry+maxPeriod+1);j++){
  const a=hist[entry],b=hist[j],delta=b.h-a.h;if(a.q!==b.q)continue;
  for(const right of [true,false]){
   if(right?delta<0:delta>0)continue;
   let boundary=right?Infinity:-Infinity;
   for(let t=entry;t<j;t++)boundary=right?Math.min(boundary,hist[t].h):Math.max(boundary,hist[t].h);
   let ok=true;
   for(const x of a.ones)if((right?x>=boundary:x<=boundary)&&!b.ones.has(x+delta)){ok=false;break;}
   if(!ok)continue;
   for(const y of b.ones)if((right?y-delta>=boundary:y-delta<=boundary)&&!a.ones.has(y-delta)){ok=false;break;}
   if(ok)return {entry,period:j-entry,right,boundary};
  }
 }
 return null;
}
const long4=[],long5=[];
for(const d of dCodes)for(let f=1;f<=25;f++){
 const p=root.slice();p[7]=d;p[10]=f;
 const r2=trace(p),w2=sideWitness(r2.hist);if(w2||r2.kind!=="unknown")continue;
 for(let a=1;a<=25;a++){
  p[r2.slot]=a;const r3=trace(p),w3=sideWitness(r3.hist);
  if(w3||r3.kind!=="unknown"){p[r2.slot]=0;continue;}
  for(let b=1;b<=25;b++){
   p[r3.slot]=b;const r4=trace(p),w4=sideWitness(r4.hist);
   if(w4){p[r3.slot]=0;continue;}
   if(r4.kind==="long"){long4.push(p.slice());p[r3.slot]=0;continue;}
   if(r4.kind==="unknown")for(let x=1;x<=25;x++){
    p[r4.slot]=x;const r5=trace(p),w5=sideWitness(r5.hist);
    if(!w5&&r5.kind==="long")long5.push(p.slice());
    p[r4.slot]=0;
   }
   p[r3.slot]=0;
  }
  p[r2.slot]=0;
 }
}
assert.equal(long4.length,69);assert.equal(long5.length,2832);
function recover(xs){
 const out=[];
 for(const p of xs){
  const r=trace(p,1000),w=sideWitness(r.hist,500,200);
  if(w)out.push({codes:p.slice(),...w});
 }
 return out;
}
const f=[...recover(long4),...recover(long5)];
const fixed=new Set([0,2,4,6]);
const hist={};
for(const w of f){
 const k=w.codes.filter((x,i)=>x!==0&&!fixed.has(i)).length;
 hist[k]=(hist[k]??0)+1;
}
assert.deepEqual(hist,{"4":4,"5":477});
assert.equal(f.length,481);
const volume=f.reduce((a,w)=>a+25n**BigInt(8-w.codes.filter((x,i)=>x!==0&&!fixed.has(i)).length),0n);
assert.equal(volume,9015625n);
function swapCode(c){if(c<=1)return c;const st=(c-2)%6;return st===4?c+1:st===5?c-1:c;}
function swapTable(p){const out=p.map(swapCode);for(let bit=0;bit<=1;bit++){out[8+bit]=swapCode(p[10+bit]);out[10+bit]=swapCode(p[8+bit]);}return out;}
const e=f.map(w=>({...w,codes:swapTable(w.codes)}));
for(let i=0;i<f.length;i++)assert.deepEqual(swapTable(e[i].codes),f[i].codes);
function emit(kind,xs){
 const module=`Raw34${kind}ExtendedLongSidecycles`;
 const ns=`BB6.Agent50ExtendedLong.${module}`;
 const src=`import Raw34D1RDOneStepCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ${ns}
open BB6Coverage BB6.Agent23Raw34Next BB6Coverage.Agent50SideCycle
structure CycleWitness where
  codes : List Nat
  entry : Nat
  period : Nat
  right : Bool
  boundary : Int
def witnesses : List CycleWitness := [
${xs.map(w=>`  ⟨[${w.codes.join(",")}], ${w.entry}, ${w.period}, ${w.right}, ${w.boundary}⟩`).join(",\n")}
]
def checkCycle (w : CycleWitness) : Bool :=
  decide (0 < w.period) &&
    fastSideCycleCheck (table w.codes) w.entry w.period w.right w.boundary
theorem count : witnesses.length = ${xs.length} := by decide
theorem checked : witnesses.all checkCycle = true := by decide +kernel
theorem all_never (w : CycleWitness) (hw : w ∈ witnesses)
    (m : Machine) (hm : compatible (table w.codes) m) : NeverHalts m := by
  have hh : checkCycle w = true := List.all_eq_true.mp checked w hw
  obtain ⟨hp,hc⟩ : decide (0 < w.period) = true ∧
      fastSideCycleCheck (table w.codes) w.entry w.period w.right w.boundary = true := by
    simpa only [checkCycle, Bool.and_eq_true] using hh
  exact fastSideCycleCheck_sound (table w.codes)
    w.entry w.period w.right w.boundary (of_decide_eq_true hp) hc m hm
#print axioms count
#print axioms checked
#print axioms all_never
end ${ns}
`;
 writeFileSync(join(output,module+".lean"),src);
 return {module,namespace:ns,count:xs.length};
}
const modules=[emit("F",f),emit("E",e)];
const report={status:"extended-window candidates; Lean source checker authoritative",
  fCount:f.length,eCount:e.length,fFixedHistogram:hist,
  grossPhysicalEach:String(volume),grossPhysicalBothBeforeOverlap:String(volume*2n),
  search:{oldCap:100,oldEntry:60,oldPeriod:30,newCap:1000,newEntry:500,newPeriod:200},
  modules};
writeFileSync(join(output,"manifest.json"),JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify(report,null,2));
