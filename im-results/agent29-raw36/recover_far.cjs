#!/usr/bin/env node
"use strict";
/* Search *sound* one-sided FAR certificates for the Raw36 holes formerly
   misclassified by the broken early-return fixed point.

   Enumerates every valid rooted binary DFA of 1..MAX_D states (up to 4 by
   default), both directions. All returned witnesses are independently
   rechecked from scratch by makeSearch.far's corrected fixed-point algorithm;
   the Lean generator will subsequently recheck them again in original
   source via the independent masks() implementation.
*/
const fs = require("fs");
const {makeSearch} = require("./search.cjs");
const spec = JSON.parse(fs.readFileSync(__dirname + "/candidate.json","utf8"));
const target = process.argv[2];
const maxD = +(process.argv[3] || 4);
const indices = (process.argv.slice(4).length ? process.argv.slice(4).map(Number) :
   [4,10,16,18,19,20,22]);
if (!target || !Number.isInteger(maxD) || maxD < 1 || maxD > 4)
  throw Error("node recover_far.cjs OUT.json MAX_D<=4 [indices]");
const base = makeSearch(spec.codes,spec.options);
const opened = [];
for (const i of indices) {
  const p=base.parse(spec.parent); p[spec.query[2]]=i;
  const z=base.run(p);
  console.log("Raw36 C1",i,"open",z.stats.open,"haltingScore",z.stats.score);
  for (const s of z.opens) opened.push({i,table:s,p:base.parse(s)});
}
const codes=[];
const old=new Set(spec.codes);
for(let d=1;d<=maxD;d++) {
  const len=2*d-1, lim=d**len;
  for(let v=0;v<lim;v++){
    let x=v, suffix="";
    for(let k=0;k<len;k++){suffix=(x%d)+suffix;x=Math.floor(x/d);}
    for(const rev of ["0","1"]) {
      const code=rev+"0"+suffix;
      if (!old.has(code)) codes.push(code);
    }
  }
}
const bank=makeSearch(codes,spec.options).bank;
console.log("Open leaves",opened.length,"new rooted DFA candidates",bank.length);
const chosen=[], recoveries=[], unresolved=[];
for(let i=0;i<opened.length;i++) {
  const leaf=opened[i];let hit=null;
  for(const c of chosen){if(base.far(leaf.p,c)){hit=c;break;}}
  if(!hit){
    for(const c of bank){if(base.far(leaf.p,c)){chosen.push(c);hit=c;break;}}
  }
  if(hit) recoveries.push({i:leaf.i,table:leaf.table,code:hit.code});
  else unresolved.push({i:leaf.i,table:leaf.table});
  if((i+1)%25===0)console.log("checked",i+1,"of",opened.length,
       "covered",recoveries.length,"remaining",unresolved.length,
       "chosen automata",chosen.length);
}
const out={maxD,candidates:bank.length,opened:opened.length,
  recovered:recoveries.length,unresolved:unresolved.length,
  codes:chosen.map(c=>c.code),recoveries,unresolvedTables:unresolved,
  provenance:{correctedSearch:"least-fixed-point FAR",indices}};
fs.writeFileSync(target,JSON.stringify(out,null,2)+"\n");
console.log("RESULT",JSON.stringify({opened:out.opened,recovered:out.recovered,
  unresolved:out.unresolved,codes:out.codes}));
