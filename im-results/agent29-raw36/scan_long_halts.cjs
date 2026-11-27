#!/usr/bin/env node
"use strict";
/** A bounded direct blank-tape replay of exact one-/few-hole Raw36 leaves,
 * discovered only after correcting the FAR fixed-point bug. Never count an
 * unqueried missing instruction as nonhalting; that verdict is only UNKNOWN.
 * On a newly reached missing row report the exact literal table, step count,
 * head position and state. A later Lean exact_halt proof is necessary for
 * publishable lower bounds.
 */
const fs=require("fs");
const {makeSearch}=require("./search.cjs");
const spec=JSON.parse(fs.readFileSync(__dirname+"/candidate.json","utf8"));
const groups=[[4],[10],[16],[18],[19],[20],[22]];
const out=process.argv[2], g=+process.argv[3],cap=+(process.argv[4]||1000000);
if(!out||!Number.isInteger(g)||g<0||g>=groups.length||!Number.isInteger(cap)||cap<6001)
  throw Error("node scan_long_halts.cjs OUTPUT GROUP0..6 STEPLIMIT>6000");
const search=makeSearch(spec.codes,spec.options);
const result={group:g,cap,leaves:0,status:{},halts:[],opens:[]};
for(const i of groups[g]){
 const p=search.parse(spec.parent);p[spec.query[2]]=i;
 const leaves=search.run(p).opens;
 for(let z=0;z<leaves.length;z++){
   const table=leaves[z],code=search.parse(table),tape=new Map();
   let state=0,head=0,n=0,bad=-1,maxHead=0;
   for(;n<=cap;n++){
     const b=tape.get(head)||0,slot=2*state+b,action=code[slot];
     if(action<0){bad=slot;break}
     const newBit=(action/12)|0, right=action%12>=6;
     if(newBit)tape.set(head,1);else tape.delete(head);
     head+=right?1:-1;
     if(Math.abs(head)>maxHead)maxHead=Math.abs(head);
     state=action%6;
   }
   result.leaves++;
   const status=bad>=0?"queryHole":"limit";
   result.status[status]=(result.status[status]||0)+1;
   const row={i,index:z,table,status,
     steps:Math.min(n,cap),query:bad,remainingHoles:code.filter(x=>x<0).length,
     head,state,maxHead,ones:tape.size};
   if(bad>=0)result.halts.push(row);else result.opens.push(row);
 }
 console.log("replayed C1=",i,"total unresolved before scan",leaves.length,
   "newly queried unassigned",result.halts.length,"still not queried",result.opens.length);
}
result.halts.sort((a,b)=>b.steps-a.steps);
result.opens.sort((a,b)=>b.maxHead-a.maxHead);
fs.writeFileSync(out,JSON.stringify(result,null,2)+"\n");
console.log("SIMULATION",JSON.stringify({group:g,cap,leaves:result.leaves,
 status:result.status,largestNewHalt:result.halts[0]||null,
 mostHeadDrift:result.opens[0]||null}));
