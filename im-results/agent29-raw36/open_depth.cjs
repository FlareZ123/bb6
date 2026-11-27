#!/usr/bin/env node
"use strict";
/** Corrected-Raw36 reopened leaf morphology and a deeper, non-certifying
 * classifier. We avoid repeating the large parent audit: only previously
 * OPEN tables are revisited with 6000 steps and max period 384.
 * No saved candidate classification is silently treated as proof.
 */
const fs=require("fs");
const {makeSearch}=require("./search.cjs");
const spec=JSON.parse(fs.readFileSync(__dirname+"/candidate.json","utf8"));
const out=process.argv[2],group=+(process.argv[3]);
if(!out||![0,1,2,3].includes(group))throw Error("Usage node open_depth.cjs OUT.json GROUP");
const sets=[[4],[10],[16],[18,19,20,22]];
const original=makeSearch(spec.codes,spec.options);
const depth=makeSearch(spec.codes,{short:6000,period:384,long:6000,longPeriod:384,maxNodes:1000000});
const summary={group,original:0,holes:{},deeper:{},cases:[],hard:[]};
for(const i of sets[group]){
  const p=original.parse(spec.parent);p[spec.query[2]]=i;
  const classification=original.run(p);
  console.log("original",i,classification.stats);
  for(const leaf of classification.opens) {
    const tape=original.parse(leaf),holes=tape.filter(x=>x===-1).length;
    summary.original++;
    summary.holes[holes]=(summary.holes[holes]||0)+1;
    const z=depth.long(tape),kind=z[0];
    summary.deeper[kind]=(summary.deeper[kind]||0)+1;
    const row={i,holes,table:leaf,kind,code:z.slice(1)};
    summary.cases.push(row);
    if(kind==="open")summary.hard.push(row);
  }
  console.log("completed",i,"original open",classification.stats.open);
}
fs.writeFileSync(out,JSON.stringify(summary,null,2)+"\n");
console.log("MORPHOLOGY",JSON.stringify({group,original:summary.original,
   holes:summary.holes,deeper:summary.deeper,
   stillOpen:summary.hard.length,sample:summary.hard.slice(0,4)}));
