#!/usr/bin/env node
"use strict";
/*
Original-source finite first-hole certificates for the 97 short exceptional
leaves of the zero-cap q0-150 source-normalized 5,905,429-node candidate.
This script is UNTRUSTED discovery output: Lean rechecks every primitive
packed step in `by decide +kernel`; LAST P reads the original unknown slot.
*/
const fs=require("node:fs"),path=require("node:path");
const dir=process.argv[2],single=process.argv[3]===undefined?null:Number(process.argv[3]);
if(!dir||single!==null&&(!Number.isInteger(single)||single<0||single>106))throw Error("usage: node generate-q0150-short-leaves.cjs OUTPUTDIR [0..106]");
const data=require("./q0-150-complete-frontier.json");
if(data.id!==150||data.table!=="1RB1LC_1RC---_0LA1LD_------_------_------"||data.opens.length!==107||data.stats.cap!==0)throw Error("unverified source frontier");
const never=new Set([
 "1RB1LC_1RC1RB_0LA1LD_1LA0RE_1RD1RF_---1RD",
 "1RB1LC_1RC0RE_0LA1LD_1LA1RE_---0RF_1LC1RD",
 "1RB1LC_1RC0RE_0LA1LD_0RB1LC_---1RF_0LA1RB",
 "1RB1LC_1RC0RE_0LA1LD_0RB1LC_---1RF_0LD1RB",
 "1RB1LC_1RC0RE_0LA1LD_0RB1LC_---1RF_0RD1RB"
]);
const long=new Map([
 ["1RB1LC_1RC1RF_0LA1LD_0LB0RE_0LC1RD_1RA---",13007746],
 ["1RB1LC_1RC1RF_0LA1LD_0LE0RB_1LA---_1RA0LA",1102620],
 ["1RB1LC_1RC1RF_0LA1LD_1LE0RB_0LA---_1RA0LA",1102608],
 ["1RB1LC_1RC1RF_0LA1LD_1LE0RB_0RA---_1RA0LA",1102620],
 ["1RB1LC_1RC1RF_0LA1LD_1LE0RB_0LB---_1RA0LA",2625198]
]);
function P(i,t){
 const ns="Raw11Q0150Short"+i;const name="BB6."+ns;const p="p";
 const bool=b=>b?"true":"false";
 const rows=t.map((m,j)=>m==="---"?"":`  | ${j>>1},${bool(m[1]==="1")} => some (some ⟨${bool(m[0]==="1")},${bool(m[1]==="R")},${m.charCodeAt(2)-65}⟩)\n`).join("");
 let lines=[
 "import FastPhaseTree","import CachedPhaseTree","import PhaseFrontier","import ExactOneHoleOrdinary",
 "set_option maxHeartbeats 0","set_option maxRecDepth 1000000",
 `namespace ${name}`,
 "open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree",
 "open BB6Coverage.Agent13PackedZipper BB6.Agent5FastPhaseTree",
 "def p : PartialMachine := fun s => match s.1.val,s.2 with",
 ...t.map((m,j)=>m==="---"?null:`  | ${j>>1},${bool(j%2)} => some (some ⟨${bool(m[0]==="1")},${bool(m[1]==="R")},${m.charCodeAt(2)-65}⟩)`).filter(x=>x!==null),
 "  | _,_ => none", "def z0 : P := startP",
 "theorem joinAt (n k t : Nat) (a b c : P) (ht : n+k=t) (h : runP p n a = some b) (g : runP p k b = some c) : runP p t a = some c := by",
 "  rw [← ht]",
 "  exact joinP h g"
 ];
 let q=0,l=0n,r=0n,prev=0,n=0;
 for(n=1;n<=100000;n++){
  const slot=2*q+Number(l&1n),m=t[slot];
  if(m==="---"){n--;break;}
  if(!m||m.length!==3)throw Error("invalid input leaf");
  const w=BigInt(m[0]);q=m.charCodeAt(2)-65;
  if(m[1]==="R"){l=(r&1n)+2n*(w+2n*(l>>1n));r>>=1n;}
  else{l>>=1n;r=w+2n*r;}
  if(n%256===0){const z="z"+n,prevZ="z"+prev,step="step"+n,run="run"+n;lines.push(`def ${z} : P := ⟨${q},${l},${r}⟩`);lines.push(`theorem ${step} : runP p ${n-prev} ${prevZ} = some ${z} := by decide +kernel`);lines.push(`theorem ${run} : runP p ${n} startP = some ${z} := ${prev===0?step:("joinAt "+prev+" "+(n-prev)+" "+n+" startP z"+prev+" z"+n+" (by decide) run"+prev+" "+step)}`);prev=n;}
 }
 if(n>=100000||t[2*q+Number(l&1n)]!=="---")throw Error("not a first-hole short leaf "+i);
 if(prev!==n){const z="z"+n,step="step"+n,run="run"+n;lines.push(`def ${z} : P := ⟨${q},${l},${r}⟩`);lines.push(`theorem ${step} : runP p ${n-prev} z${prev} = some ${z} := by decide +kernel`);lines.push(`theorem ${run} : runP p ${n} startP = some ${z} := ${prev===0?step:("joinAt "+prev+" "+(n-prev)+" "+n+" startP z"+prev+" z"+n+" (by decide) run"+prev+" "+step)}`);}
 const slot=2*q+Number(l&1n),cert=`theorem safe : ∀ m, compatible p m → WeightedBound 13007752 m :=\n  lastPacked 13007752 p ${n} (${q},${bool(slot%2)}) z${n} run${n} (by decide) (by decide) (by decide) (by decide) (by decide)`;
 const exact=`theorem exact : ∀ m, compatible p m → BB6.Agent5ExactOneHole.OrdinaryBound 13007747 m :=\n  BB6.Agent5ExactOneHole.lastPackedExact 13007747 p ${n} (${q},${bool(slot%2)}) z${n} run${n} (by decide) (by decide) (by decide) (by decide)`;
 lines.push(cert,exact,"#print axioms safe","#print axioms exact",`end ${name}`,"");
 const filename=ns+".lean";fs.writeFileSync(path.join(dir,filename),lines.join("\n"));
 return {index:i,steps:n,slot,table:Array.from({length:6},(_,j)=>t[2*j]+t[2*j+1]).join("_"),module:ns,filename};
}
fs.mkdirSync(dir,{recursive:true});
let labels=[],short=0,longN=0,inf=0;
for(let i=0;i<data.opens.length;i++){
 const s=data.opens[i],t=s.split("_");if(t.length!==6||t.some(x=>x.length!==6)||t.flatMap(x=>x.match(/.{3}/g)).filter(x=>x==="---").length!==1)throw Error("not exact one-hole leaf index "+i);
 if(never.has(s)){inf++;labels.push({index:i,type:"never",table:s});continue;}
 if(long.has(s)){longN++;labels.push({index:i,type:"long",table:s,steps:long.get(s)});continue;}
 if(single===null||single===i){const x=P(i,t.flatMap(x=>x.match(/.{3}/g)));labels.push({type:"short",...x});short++;}
 else{labels.push({index:i,type:"short-skipped",table:s});}
}
if(single===null&&(short!==97||longN!==5||inf!==5))throw Error("wrong census counts "+JSON.stringify({short,longN,inf}));
fs.writeFileSync(path.join(dir,"manifest.json"),JSON.stringify({root:data.table,bound:13007752,shortGenerated:short,long:longN,never:inf,leaves:labels},null,2));
console.log(JSON.stringify({dir,short,longN,inf,maxShort:Math.max(...labels.filter(x=>x.type==="short").map(x=>x.steps))}));
