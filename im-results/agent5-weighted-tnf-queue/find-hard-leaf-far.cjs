#!/usr/bin/env node
"use strict";
// Targeted regular-language nonhalting certificate discovery for the only
// difficult post-frontier leaves of q0-148 and q0-151, NOT a simulation.
const fs=require("node:fs"),path=require("node:path");
const {solve,emit}=require("./q0-open-automata.cjs");
const {blockFAR}=require("./phase-tree/block-phase-far.cjs");
const cases={
 "148":{name:"Q0148HardF1",table:"1RB1LC1RC0RE0LA0LD1LA0RF1RB1RD0RC---"},
 "151":{name:"Q0151HardF0",table:"1RB1LC1RC0RD0LA1RD1RB0RE1LC1RF---0RC"}
};
const row=cases[process.argv[2]],out=process.argv[3]||"/tmp/q0-hard-far",capSec=Number(process.argv[4]||600);
if(!row)throw Error("usage: node find-hard-leaf-far.cjs 148|151 OUTPUTDIR [maxSeconds=600]");
fs.mkdirSync(out,{recursive:true});
const st=Date.now(),maxMs=capSec*1000;
let attempts=0,cand=null,winner=null,tries=[];
function tryParam(kind,k,mirror,cap=2,depth=2,limit=90000,block=false){
 if(Date.now()-st>maxMs)return false;
 attempts++;let x;
 try{x=block?blockFAR(row.table,k,cap,kind,mirror,2,depth,limit):solve(row.table,k,kind,mirror,limit,cap,depth);}
 catch(e){tries.push({kind,k,mirror,cap,depth,error:String(e)});return false}
 if(x){
   cand=x;winner={kind,k,mirror,cap,depth,block,attempt:attempts};
   const info={table:row.table,winner,source:"preflight regular-language witness; check Lean original source separately",rows:x.rows?.length??null};
   fs.writeFileSync(path.join(out,"winner.json"),JSON.stringify(info,null,2));
   const ns="BB6.Agent5HardFAR."+row.name;
   let src="import TwoSidedAutomata\nimport WeightedTNF\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nopen BB6Coverage BB6.Agent13BlankDelay\n"+emit(x,ns);
   src+=`\nnamespace ${ns}\ntheorem cover (B : Nat) : Cover (WeightedBound B) table :=\n  .leaf _ fun m hm => weighted_never B m (never m hm)\n#print axioms cover\nend ${ns}\n`;
   fs.writeFileSync(path.join(out,row.name+".lean"),src);
   console.log("SUCCESS "+JSON.stringify(info));return true;
 }
 if(attempts%30===0)console.log("checked "+attempts+" configurations in "+Math.round((Date.now()-st)/1000)+"s");
 return false;
}
function progressPhases(){
 // Preserve exact source checking; discovery code may be wrong.
 for(const k of [8,10,12,14,16,18])for(const mirror of [false,true])if(tryParam("ngram",k,mirror,2,2,140000))return true;
 // Density-adapted regular summaries: 151 has long 111110 runs,
 // 148 has long alternating runs punctuated by occasional defects.
 const lags=process.argv[2]==="148"?[2,3,4,6]:[6,3,2,4];
 for(const lag of lags)for(const depth of [2,3,4,5])for(const mod of [2,3,4,6,8,12])for(const mirror of [false,true]){
   if(tryParam("lag"+lag,mod,mirror,2,depth,110000))return true;
 }
 for(const width of [2,3,4,5,6])for(const depth of [2,3])for(const mod of [2,3,4,6])for(const mirror of [false,true]){
   if(tryParam("blk"+width,mod,mirror,2,depth,110000))return true;
 }
 if(Date.now()-st<maxMs/2)for(const width of [2,3,4])for(const mod of [2,3,4])for(const depth of [2,3])for(const mirror of [false,true]){
   if(tryParam("run",width,mirror,2,depth,110000,true))return true;
 }
 return false;
}
progressPhases();
fs.writeFileSync(path.join(out,"summary.json"),JSON.stringify({
 table:row.table,winner,attempts,elapsed_ms:Date.now()-st,errors:tries.slice(0,20)
},null,2));
console.log("FINAL "+JSON.stringify({winner,attempts,elapsed_ms:Date.now()-st}));
