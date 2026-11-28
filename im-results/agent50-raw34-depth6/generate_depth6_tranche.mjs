#!/usr/bin/env node
/**
 * Deterministic 100k Raw34 F depth-six first-query sidecycle tranche plus
 * direct E/F-state conjugates.  Search only proposes witnesses; emitted Lean
 * source rechecks every row with fastSideCycleCheck_sound.
 */
import assert from "node:assert/strict";
import {mkdirSync,writeFileSync} from "node:fs";
import {join} from "node:path";
const args=process.argv.slice(2);
function opt(name,def){const i=args.indexOf(name);return i<0?def:args[i+1];}
const output=opt("--output","/tmp/a50-raw34-depth6");
const limit=Number(opt("--limit","100000"));
const shardSize=Number(opt("--shard-size","200"));
assert(Number.isInteger(limit)&&limit>0&&limit<=100000);
assert(Number.isInteger(shardSize)&&shardSize>0);
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
function sideWitness(hist){
 const max=Math.min(hist.length,60);
 for(let entry=0;entry<max;entry++)
 for(let j=entry+1;j<Math.min(hist.length,entry+31);j++){
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
const earlier=[],open5=[],selected=[];
const stats={old2:0,old3:0,old4:0,cycle5:0,open5:0,long5:0,halt5:0,
 depth6Examined:0,cycle6Selected:0};
for(const d of dCodes)for(let f=1;f<=25;f++){
 const p=root.slice();p[7]=d;p[10]=f;
 const path2=[{slot:7,code:d},{slot:10,code:f}];
 const r2=trace(p),w2=sideWitness(r2.hist);
 if(w2){stats.old2++;earlier.push({path:path2});continue;}
 if(r2.kind!=="unknown")continue;
 for(let a=1;a<=25;a++){
  p[r2.slot]=a;const path3=path2.concat({slot:r2.slot,code:a});
  const r3=trace(p),w3=sideWitness(r3.hist);
  if(w3){stats.old3++;earlier.push({path:path3});p[r2.slot]=0;continue;}
  if(r3.kind!=="unknown"){p[r2.slot]=0;continue;}
  for(let b=1;b<=25;b++){
   p[r3.slot]=b;const path4=path3.concat({slot:r3.slot,code:b});
   const r4=trace(p),w4=sideWitness(r4.hist);
   if(w4){stats.old4++;earlier.push({path:path4});p[r3.slot]=0;continue;}
   if(r4.kind==="unknown")for(let x=1;x<=25;x++){
    p[r4.slot]=x;const path5=path4.concat({slot:r4.slot,code:x});
    const r5=trace(p),w5=sideWitness(r5.hist);
    if(w5){stats.cycle5++;earlier.push({path:path5});}
    else if(r5.kind==="halt")stats.halt5++;
    else if(r5.kind==="unknown"){stats.open5++;open5.push({codes:p.slice(),path:path5,slot:r5.slot});}
    else stats.long5++;
    p[r4.slot]=0;
   }
   p[r3.slot]=0;
  }
  p[r2.slot]=0;
 }
}
assert.deepEqual({
 old2:stats.old2,old3:stats.old3,old4:stats.old4,cycle5:stats.cycle5,
 open5:stats.open5,long5:stats.long5,halt5:stats.halt5
},{old2:34,old3:592,old4:9231,cycle5:150895,open5:138017,long5:2832,halt5:12156});
outer: for(const par of open5){
 const p=par.codes.slice();
 for(let x=1;x<=25;x++){
  p[par.slot]=x;stats.depth6Examined++;
  const r=trace(p),w=sideWitness(r.hist);
  if(w){
   selected.push({codes:p.slice(),path:par.path.concat({slot:par.slot,code:x}),...w});
   stats.cycle6Selected++;
   if(selected.length===limit)break outer;
  }
 }
}
assert.equal(selected.length,limit);
function verifyPrefixTree(leaves){
 const root={slot:null,children:new Map(),leaf:false};
 for(const leaf of leaves){
  let n=root;
  for(const e of leaf.path){
   assert(!n.leaf,"prefix collision");
   if(n.slot===null)n.slot=e.slot;else assert.equal(n.slot,e.slot,"prefix-determined queried slot");
   if(!n.children.has(e.code))n.children.set(e.code,{slot:null,children:new Map(),leaf:false});
   n=n.children.get(e.code);
  }
  assert(!n.leaf&&n.children.size===0,"duplicate/prefix leaf");n.leaf=true;
 }
}
verifyPrefixTree(earlier.concat(selected));
const gross=BigInt(limit)*25n**2n;
assert.equal(gross,BigInt(limit)*625n);
function swapCode(c){if(c<=1)return c;const st=(c-2)%6;return st===4?c+1:st===5?c-1:c;}
function swapTable(p){const out=p.map(swapCode);for(let bit=0;bit<=1;bit++){out[8+bit]=swapCode(p[10+bit]);out[10+bit]=swapCode(p[8+bit]);}return out;}
const eSelected=selected.map(w=>({...w,codes:swapTable(w.codes)}));
for(let i=0;i<selected.length;i++)assert.deepEqual(swapTable(eSelected[i].codes),selected[i].codes);
function emit(kind,xs){
 const modules=[];
 for(let i=0;i<Math.ceil(xs.length/shardSize);i++){
  const ys=xs.slice(i*shardSize,(i+1)*shardSize),suffix=String(i).padStart(3,"0");
  const module=`Raw34${kind}Depth6SideShard${suffix}`;
  const ns=`BB6.Agent50Depth6.${module}`;modules.push({module,namespace:ns,size:ys.length});
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
${ys.map(w=>`  ⟨[${w.codes.join(",")}], ${w.entry}, ${w.period}, ${w.right}, ${w.boundary}⟩`).join(",\n")}
]
def checkCycle (w : CycleWitness) : Bool :=
  decide (0 < w.period) &&
    fastSideCycleCheck (table w.codes) w.entry w.period w.right w.boundary
theorem count : witnesses.length = ${ys.length} := by decide
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
 }
 return modules;
}
const fModules=emit("F",selected),eModules=emit("E",eSelected);
const report={status:"depth-six deterministic tranche; Lean source checker authoritative",
 limit,shardSize,grossPhysicalEach:String(gross),grossPhysicalBothBeforeOverlap:String(2n*gross),
 prefixTreeDisjointnessChecked:true,earlierFCycleLeaves:earlier.length,stats,fModules,eModules};
writeFileSync(join(output,"manifest.json"),JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify({...report,fModules:fModules.length,eModules:eModules.length},null,2));
