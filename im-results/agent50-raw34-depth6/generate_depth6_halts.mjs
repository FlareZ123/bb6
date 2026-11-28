#!/usr/bin/env node
/**
 * Raw34 direct-halting children of the depth-five F frontier, plus exact
 * E/F-state conjugates.  Each open depth-five prefix reaches one genuine next
 * undefined instruction; assigning physical HALT to that slot gives an
 * all-completions finite halt cylinder.  Generated Lean rechecks the original
 * finiteHaltCheck semantics; the enumeration is not trusted.
 */
import assert from "node:assert/strict";
import {mkdirSync,writeFileSync} from "node:fs";
import {join} from "node:path";
const args=process.argv.slice(2);
function opt(name,def){const i=args.indexOf(name);return i<0?def:args[i+1];}
const output=opt("--output","/tmp/a50-raw34-depth6-halts");
const limit=Number(opt("--limit","138017"));
const shardSize=Number(opt("--shard-size","250"));
assert(Number.isInteger(limit)&&limit>0&&limit<=138017);
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
  const v=action-2;v>=12?ones.add(h):ones.delete(h);
  q=v%6;h+=v%12>=6?1:-1;
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
   for(let t=entry;t<j;t++)
    boundary=right?Math.min(boundary,hist[t].h):Math.max(boundary,hist[t].h);
   let ok=true;
   for(const x of a.ones)
    if((right?x>=boundary:x<=boundary)&&!b.ones.has(x+delta)){ok=false;break;}
   if(!ok)continue;
   for(const y of b.ones)
    if((right?y-delta>=boundary:y-delta<=boundary)&&!a.ones.has(y-delta)){ok=false;break;}
   if(ok)return {entry,period:j-entry,right,boundary};
  }
 }
 return null;
}
const open5=[],earlier=[];
const stats={old2:0,old3:0,old4:0,cycle5:0,halt5:0,open5:0,long5:0};
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
    else if(r5.kind==="unknown"){
      stats.open5++;
      open5.push({codes:p.slice(),path:path5,slot:r5.slot,n:r5.t});
    } else stats.long5++;
    p[r4.slot]=0;
   }
   p[r3.slot]=0;
  }
  p[r2.slot]=0;
 }
}
assert.deepEqual(stats,{old2:34,old3:592,old4:9231,cycle5:150895,
 halt5:12156,open5:138017,long5:2832});
assert.equal(open5.length,138017);

const fHalts=open5.slice(0,limit).map(x=>{
 const codes=x.codes.slice();assert.equal(codes[x.slot],0);codes[x.slot]=1;
 const r=trace(codes);assert.equal(r.kind,"halt");assert.equal(r.t,x.n);
 return {codes,n:x.n,path:x.path.concat({slot:x.slot,code:1})};
});
const maxHalt=Math.max(...fHalts.map(x=>x.n));
assert(maxHalt<=100);

function verifyPrefixTree(leaves){
 const root={slot:null,children:new Map(),leaf:false};
 for(const leaf of leaves){
  let n=root;
  for(const e of leaf.path){
   assert(!n.leaf,"prefix collision");
   if(n.slot===null)n.slot=e.slot;else assert.equal(n.slot,e.slot,"prefix-determined next query");
   if(!n.children.has(e.code))n.children.set(e.code,{slot:null,children:new Map(),leaf:false});
   n=n.children.get(e.code);
  }
  assert(!n.leaf&&n.children.size===0,"duplicate/prefix leaf");n.leaf=true;
 }
}
verifyPrefixTree(earlier.concat(fHalts));

function swapCode(c){if(c<=1)return c;const st=(c-2)%6;return st===4?c+1:st===5?c-1:c;}
function swapTable(p){
 const out=p.map(swapCode);
 for(let bit=0;bit<=1;bit++){out[8+bit]=swapCode(p[10+bit]);out[10+bit]=swapCode(p[8+bit]);}
 return out;
}
const eHalts=fHalts.map(w=>({...w,codes:swapTable(w.codes)}));
for(let i=0;i<fHalts.length;i++)assert.deepEqual(swapTable(eHalts[i].codes),fHalts[i].codes);

function emit(kind,xs){
 const modules=[];
 for(let i=0;i<Math.ceil(xs.length/shardSize);i++){
  const ys=xs.slice(i*shardSize,(i+1)*shardSize),suffix=String(i).padStart(3,"0");
  const module=`Raw34${kind}Depth6HaltShard${suffix}`;
  const ns=`BB6.Agent50Depth6Halt.${module}`;
  modules.push({module,namespace:ns,size:ys.length});
  const source=`import Raw34EarlyHaltersSound
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ${ns}
open BB6Coverage BB6.Agent23Raw34Next BB6.Agent40Raw34EarlyHalters
structure HaltWitness where
  codes : List Nat
  n : Nat
def witnesses : List HaltWitness := [
${ys.map(w=>`  ⟨[${w.codes.join(",")}], ${w.n}⟩`).join(",\n")}
]
def checkHalt (w : HaltWitness) : Bool :=
  finiteHaltCheck (table w.codes) w.n
theorem count : witnesses.length = ${ys.length} := by decide
theorem checked : witnesses.all checkHalt = true := by decide +kernel
theorem all_halt (w : HaltWitness) (hw : w ∈ witnesses)
    (m : Machine) (hm : compatible (table w.codes) m) :
    HaltsAfter m w.n := by
  have hh : checkHalt w = true := List.all_eq_true.mp checked w hw
  exact finite_check_exact_halt (table w.codes) w.n m hm hh
#print axioms count
#print axioms checked
#print axioms all_halt
end ${ns}
`;
  writeFileSync(join(output,module+".lean"),source);
 }
 return modules;
}
const fModules=emit("F",fHalts),eModules=emit("E",eHalts);
const gross=BigInt(limit)*25n**2n;
const report={
 status:"direct sixth-query HALT cylinders; original finite semantics source checker authoritative",
 totalOpenDepth5:open5.length,selectedCount:limit,maxHalt,
 grossPhysicalEach:String(gross),grossPhysicalBothBeforeOverlap:String(2n*gross),
 prefixTreeDisjointnessChecked:true,stats,fModules,eModules
};
writeFileSync(join(output,"manifest.json"),JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify({...report,fModules:fModules.length,eModules:eModules.length},null,2));
