#!/usr/bin/env node
/**
 * Raw34 F-branch fifth first-query layer.
 *
 * This continues the accepted 34/592/9,231 two/three/four-slot F side-cycle
 * tree by exactly one genuine first-undefined-instruction split.  The finite
 * simulation only proposes witnesses; every emitted NeverHalts theorem is
 * validated by the original Lean fastSideCycleCheck_sound theorem.
 *
 * A deterministic low-check-cost tranche can be selected with --limit.
 * The full census is always computed, so later runs may raise the limit
 * without changing the underlying candidate population.
 */
import assert from "node:assert/strict";
import {mkdirSync,writeFileSync} from "node:fs";
import {join} from "node:path";

const args=process.argv.slice(2);
function opt(name,def){const i=args.indexOf(name);return i<0?def:args[i+1];}
const output=opt("--output","/tmp/a50-raw34-f-depth5");
const shardSize=Number(opt("--shard-size","200"));
const limit=Number(opt("--limit","25000"));
assert(Number.isInteger(shardSize)&&shardSize>0);
assert(Number.isInteger(limit)&&limit>0);
mkdirSync(output,{recursive:true});

const alphabet=["HALT"];
for(const w of "01")for(const d of "LR")for(const q of "ABCDEF")
  alphabet.push(w+d+q);
const root=[21,0,22,0,11,0,16,0,0,0,0,0];
const dCodes=["0LF","1LF","0RF","1RF"].map(x=>alphabet.indexOf(x)+1);

function trace(p,cap=100){
  let q=0,h=0,ones=new Set(),hist=[];
  for(let t=0;t<=cap;t++){
    hist.push({q,h,ones:new Set(ones)});
    const slot=2*q+(ones.has(h)?1:0),action=p[slot];
    if(action===0||action===1)
      return {kind:action===0?"unknown":"halt",slot,hist,t};
    const v=action-2;
    v>=12?ones.add(h):ones.delete(h);
    q=v%6;h+=v%12>=6?1:-1;
  }
  return {kind:"long",hist};
}
function sideWitness(hist){
  const max=Math.min(hist.length,60);
  for(let entry=0;entry<max;entry++)
  for(let j=entry+1;j<Math.min(hist.length,entry+31);j++){
    const a=hist[entry],b=hist[j],delta=b.h-a.h;
    if(a.q!==b.q)continue;
    for(const right of [true,false]){
      if(right?delta<0:delta>0)continue;
      let boundary=right?Infinity:-Infinity;
      for(let t=entry;t<j;t++)
        boundary=right?Math.min(boundary,hist[t].h):
                       Math.max(boundary,hist[t].h);
      if([...a.ones].some(x=>(right?x>=boundary:x<=boundary)&&
          !b.ones.has(x+delta)))continue;
      if([...b.ones].some(y=>(right?y-delta>=boundary:y-delta<=boundary)&&
          !a.ones.has(y-delta)))continue;
      return {entry,period:j-entry,right,boundary};
    }
  }
  return null;
}

// A path records assignments to the eight free Raw34 root slots.
// At each tree node the next slot is forced by the genuine partial run.
const earlier=[],candidates=[];
const stats={old2:0,open2:0,old3:0,open3:0,old4:0,open4:0,
  long4:0,children5:0,cycle5:0,halt5:0,open5:0,long5:0};
for(const d of dCodes)for(let f=1;f<=25;f++){
  const p=root.slice();p[7]=d;p[10]=f;
  const path2=[{slot:7,code:d},{slot:10,code:f}];
  const r2=trace(p),w2=sideWitness(r2.hist);
  if(w2){stats.old2++;earlier.push({codes:p.slice(),path:path2});continue;}
  if(r2.kind!=="unknown")continue;
  stats.open2++;
  for(let a=1;a<=25;a++){
    p[r2.slot]=a;
    const path3=path2.concat({slot:r2.slot,code:a});
    const r3=trace(p),w3=sideWitness(r3.hist);
    if(w3){stats.old3++;earlier.push({codes:p.slice(),path:path3});
      p[r2.slot]=0;continue;}
    if(r3.kind!=="unknown"){p[r2.slot]=0;continue;}
    stats.open3++;
    for(let b=1;b<=25;b++){
      p[r3.slot]=b;
      const path4=path3.concat({slot:r3.slot,code:b});
      const r4=trace(p),w4=sideWitness(r4.hist);
      if(w4){stats.old4++;earlier.push({codes:p.slice(),path:path4});
        p[r3.slot]=0;continue;}
      if(r4.kind==="unknown"){
        stats.open4++;
        for(let x=1;x<=25;x++){
          p[r4.slot]=x;stats.children5++;
          const path5=path4.concat({slot:r4.slot,code:x});
          const r5=trace(p),w5=sideWitness(r5.hist);
          if(w5){stats.cycle5++;
            candidates.push({codes:p.slice(),path:path5,...w5});}
          else if(r5.kind==="halt")stats.halt5++;
          else if(r5.kind==="unknown")stats.open5++;
          else stats.long5++;
          p[r4.slot]=0;
        }
      }else if(r4.kind==="long")stats.long4++;
      p[r3.slot]=0;
    }
    p[r2.slot]=0;
  }
}
assert.deepEqual(stats,{old2:34,open2:62,old3:592,open3:894,
  old4:9231,open4:12156,long4:69,children5:303900,
  cycle5:150895,halt5:12156,open5:138017,long5:2832});
assert.equal(earlier.length,9857);
assert.equal(candidates.length,150895);
assert.equal(new Set(candidates.map(x=>x.codes.join(","))).size,candidates.length);

// Verify the first-query construction is a genuine prefix-free decision tree.
// This is linear in the number of leaves and gives exact pairwise cylinder
// disjointness without a quadratic all-pairs scan.
function verifyPrefixTree(leaves){
  const root={slot:null,children:new Map(),leaf:false};
  for(const leaf of leaves){
    let n=root;
    for(const e of leaf.path){
      assert(!n.leaf,"decision-tree leaf is a prefix of another leaf");
      if(n.slot===null)n.slot=e.slot;
      else assert.equal(n.slot,e.slot,"next queried slot must be prefix-determined");
      if(!n.children.has(e.code))
        n.children.set(e.code,{slot:null,children:new Map(),leaf:false});
      n=n.children.get(e.code);
    }
    assert(!n.leaf&&n.children.size===0,"duplicate or prefix collision");
    n.leaf=true;
  }
}
verifyPrefixTree(earlier.concat(candidates));
const oldGross=34n*25n**6n+592n*25n**5n+9231n*25n**4n;
const fullNewGross=BigInt(candidates.length)*25n**3n;
assert.equal(fullNewGross,2357734375n);

// All candidates have equal physical volume. Prefer the cheapest finite
// checker witnesses so a first source-gated tranche maximizes certified mass
// per CI cost without cherry-picking by machine behavior.
candidates.sort((a,b)=>(a.entry+a.period)-(b.entry+b.period)||
  a.period-b.period||a.codes.join(",").localeCompare(b.codes.join(",")));
const selected=candidates.slice(0,Math.min(limit,candidates.length));
verifyPrefixTree(earlier.concat(selected));
const selectedGross=BigInt(selected.length)*25n**3n;

const modules=[];
for(let i=0;i<Math.ceil(selected.length/shardSize);i++){
  const xs=selected.slice(i*shardSize,(i+1)*shardSize);
  const suffix=String(i).padStart(3,"0");
  const module=`Raw34FDepth5SideShard${suffix}`;
  const namespace=`BB6.Agent50FDepth5.${module}`;
  modules.push({module,namespace,size:xs.length});
  const source=`import Raw34D1RDOneStepCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-! Fifth first-query F-branch half-line recurrences.  Candidate generation
is not trusted: checked and all_never below use the original source checker. -/
namespace ${namespace}
open BB6Coverage BB6.Agent23Raw34Next BB6Coverage.Agent50SideCycle
structure CycleWitness where
  codes : List Nat
  entry : Nat
  period : Nat
  right : Bool
  boundary : Int
def witnesses : List CycleWitness := [
${xs.map(x=>`  ⟨[${x.codes.join(",")}], ${x.entry}, ${x.period}, ${x.right}, ${x.boundary}⟩`).join(",\n")}
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
      fastSideCycleCheck (table w.codes)
        w.entry w.period w.right w.boundary = true := by
    simpa only [checkCycle, Bool.and_eq_true] using hh
  exact fastSideCycleCheck_sound (table w.codes)
    w.entry w.period w.right w.boundary
    (of_decide_eq_true hp) hc m hm
#print axioms count
#print axioms checked
#print axioms all_never
end ${namespace}
`;
  writeFileSync(join(output,module+".lean"),source);
}
const report={
  status:"fifth first-query source candidates; emitted tranche requires Lean acceptance",
  root:"1RB---_1RC---_0RD---_1LC---_------_------",
  stats,previousAcceptedFDepth2to4:9857,
  previousFDepth2to4Gross:String(oldGross),
  fullNewCandidateCount:candidates.length,
  fullNewCandidateGross:String(fullNewGross),
  selectedCount:selected.length,selectedGross:String(selectedGross),
  selection:"ascending entry+period, then period, then physical code",
  prefixTreeDisjointnessChecked:true,shardSize,modules
};
writeFileSync(join(output,"manifest.json"),JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify({...report,
  modules:modules.map(x=>x.namespace+".all_never")},null,2));
