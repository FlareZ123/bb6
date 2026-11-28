#!/usr/bin/env node
"use strict";
/* This emits a proof *candidate*, not a proof bypass. The 435 outputs are
   untrusted requests to the source-checked macro lemmas; Lean verifies each. */
const fs=require("node:fs"),path=require("node:path");
const rec=require("./leaf2265.cjs");
const xs=rec.trace;
if(xs.length!==436||rec.sections!==435)throw Error("bad trace length");
const clean=s=>s.replace(/0+$/,"");
function ray(s){return "pre ["+Array.from(s,c=>c==="1"?"true":"false").join(",")+"] blank"}
function at(x){return "S "+x.k+" ("+ray(x.w)+")"}
function macro(x){
 const k=x.k,w=x.w;
 if(w.startsWith("1"))return "one "+k+" ("+ray(w.slice(1))+")";
 if(!w.startsWith("00"))throw Error("not normalized");
 const z=w+"000";let m=0;while(z[2+m]==="1")m++;
 const u=clean(z.slice(3+m)),r=Math.floor(m/4),j=m%4;
 const t=(k-(j===0?1n:0n))/2n;
 if(j===0)return (r===0?(k%2n?"zeroOddRound":"zeroEvenRound"):(k%2n?"fourOddRound":"fourEvenRound"))+" "+t+(r?" "+(r-1):"")+" ("+ray(u)+")";
 if(j===1)return (r===0?"one0010":"oneHighRound")+" "+k+(r?" "+(r-1):"")+" ("+ray(u)+")";
 if(j===2)return (!(k%2n)?"twoEvenRound "+t+" "+r:k%2n&&r?"twoOddHighRound "+t+" "+(r-1):"twoOddZeroRound "+t)+" ("+ray(u)+")";
 throw Error("unexpected early terminal");
}
let S="import Leaf2265MacroAll\n\nnamespace BB6.Agent3Leaf2265\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\n/-! Generated source-level counted 435-section candidate.\nEvery section must be independently checked by Lean against arbitrary-tail lemmas.\nNo proof acceptance is implied by source generation. -/\n\n";
const chunks=[];
for(let st=0;st<435;st+=10){
 const en=Math.min(st+10,435),ys=xs.slice(st,en),name="traceChunk"+Math.floor(st/10);
 chunks.push(name);
 S+="theorem "+name+" : Runs "+(xs[en].T-xs[st].T)+" ("+at(xs[st])+") ("+at(xs[en])+") := by\n";
 for(const x of ys){
  const y=xs[x.i+1],n=y.T-x.T;
  S+="  have s"+x.i+" : Runs "+n+" ("+at(x)+") ("+at(y)+") := by\n";
  S+="    simpa [pre, P, G, O, rep, S_push] using ("+macro(x)+")\n";
 }
 let e="s"+ys[ys.length-1].i;
 for(let i=ys.length-2;i>=0;i--)e="(chain s"+ys[i].i+" "+e+")";
 S+="  have h := "+e+"\n  simpa only [Nat.reduceAdd] using h\n\n";
}
const last=xs[435],sum=last.T-13n;
S+="theorem traceSections : Runs "+sum+" (S 3 blank) ("+at(last)+") := by\n";
let e=chunks[chunks.length-1];
for(let i=chunks.length-2;i>=0;i--)e="(chain "+chunks[i]+" "+e+")";
S+="  have h := "+e+"\n  simpa only [Nat.reduceAdd, pre] using h\n\n";
const z=last.w+"000";let m=0;while(z[2+m]==="1")m++;
if(m%4!==3)throw Error("not terminal");
const u=clean(z.slice(3+m)),r=Math.floor(m/4),cost=2n*last.k+13n+10n*BigInt(r);
if(last.T+cost!==rec.firstE0)throw Error("bad cost");
S+="def terminalCfg : Cfg := E (rep Q "+last.k+" blank)\n  (pre [false,false,false,false]\n    (rep G "+r+" (pre [true,true,true] ("+ray(u)+"))))\n\n";
S+="theorem terminalRead : terminalCfg.q = 4 ∧ terminalCfg.r 0 = false := by\n  constructor <;> rfl\n\n";
S+="theorem terminalRun : Runs "+rec.firstE0+" blankCfg terminalCfg := by\n";
S+="  have hTerm : Runs "+cost+" ("+at(last)+") terminalCfg := by\n";
S+="    simpa [pre, rep, G, O, P, terminalCfg] using\n      (terminal3 "+last.k+" "+r+" ("+ray(u)+"))\n";
S+="  have h := chain seed (chain traceSections hTerm)\n  simpa only [Nat.reduceAdd] using h\n\n";
S+="#print axioms terminalRun\n#print axioms terminalRead\nend BB6.Agent3Leaf2265\n";
const filename=path.join(__dirname,"Leaf2265Trace.lean");
if(process.argv.includes("--check")){
 if(fs.readFileSync(filename,"utf8")!==S)throw Error("generated Lean source differs; regenerate deliberately");
 console.log("Generated source byte-equal, 435 sections");
}else{
 fs.writeFileSync(filename,S);
 console.log("Generated",filename,S.length,"bytes");
}
