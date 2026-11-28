#!/usr/bin/env node
/** Exact 25-way first-unassigned refinement, pure finite discovery.
 * Audit: node next-stage.mjs ; regenerate: node next-stage.mjs --write
 */
import assert from "node:assert/strict";
import {readFileSync,writeFileSync} from "node:fs";
import {resolve,dirname} from "node:path";
import {fileURLToPath} from "node:url";
const here=dirname(fileURLToPath(import.meta.url));
const source=JSON.parse(readFileSync(resolve(here,"D1-1RD-proof-frontier.json"),"utf8"));
const alphabet=source.alphabet,states="ABCDEF",order=[7,5,3,1,8,9,10,11];
const base=["1RB",null,"1RC",null,"0RD",null,"1LC",null,null,null,null,null];
function simulate(table,budget=100){
 const ones=new Set(),hist=[];let q=0,head=0;
 for(let t=0;t<=budget;t++){
  const slot=q*2+(ones.has(head)?1:0),action=table[slot],now={q,head,ones:new Set(ones)};
  for(let i=0;i<hist.length;i++){
   const old=hist[i];if(old.q!==q)continue;
   const delta=head-old.head,heads=hist.slice(i).map(z=>z.head);
   for(const right of delta===0?[true,false]:[delta>0]){
    const boundary=right?Math.min(...heads):Math.max(...heads),side=x=>right?x>=boundary:x<=boundary;
    if([...old.ones].every(x=>!side(x)||now.ones.has(x+delta))&&
       [...now.ones].every(x=>!side(x-delta)||old.ones.has(x-delta)))
      return {kind:"side",entry:i,period:t-i,right,boundary};
   }
  }
  if(action===null)return{kind:"open",slot,step:t};
  if(action==="HALT")return{kind:"halt",slot,step:t};
  hist.push(now);if(action[0]==="1")ones.add(head);else ones.delete(head);
  head+=action[1]==="R"?1:-1;q=states.indexOf(action[2]);
 }
 return{kind:"timeout",step:budget};
}
const refined=[],counts={},masses={};let firstHaltLeaves=0;
for(let parentIndex=0;parentIndex<source.open.length;parentIndex++){
 const leaf=source.open[parentIndex],table=base.slice();
 leaf.decisions.forEach((v,i)=>{if(v!==null)table[order[i]]=v;});
 const first=simulate(table);
 if(first.kind==="halt"){firstHaltLeaves++;continue;}
 assert.equal(first.kind,"open");
 const slotIndex=order.indexOf(first.slot);assert(slotIndex>=0);
 for(const action of alphabet){
  const child=table.slice();child[first.slot]=action;
  const witness=simulate(child),decisions=leaf.decisions.slice();
  while(decisions.length<8)decisions.push(null);
  decisions[slotIndex]=action;
  const mass=25n**BigInt(8-decisions.filter(v=>v!==null).length);
  const entry={parentIndex,slot:states[Math.floor(first.slot/2)]+(first.slot%2),
    action,kind:witness.kind,mass:mass.toString()};
  if(witness.kind==="halt")Object.assign(entry,{step:witness.step});
  if(witness.kind==="side")Object.assign(entry,{
    entry:witness.entry,period:witness.period,right:witness.right,boundary:witness.boundary});
  if(witness.kind==="open")Object.assign(entry,{
    nextSlot:states[Math.floor(witness.slot/2)]+(witness.slot%2),step:witness.step});
  if(witness.kind==="timeout")Object.assign(entry,{step:witness.step});
  refined.push(entry);
  counts[witness.kind]=(counts[witness.kind]||0)+1;
  masses[witness.kind]=(BigInt(masses[witness.kind]||"0")+mass).toString();
 }
}
assert.equal(firstHaltLeaves,12);assert.equal(refined.length,3825);
assert.deepEqual(counts,{halt:153,side:1744,open:1844,timeout:84});
assert.deepEqual(masses,{halt:"97265625",side:"934375000",open:"1357812500",timeout:"42187500"});
assert.equal(Object.values(masses).reduce((a,x)=>a+BigInt(x),0n),2431640625n);
const out={description:"Finite discovery, not yet source-Lean accepted",budget:100,
 sourceParentOpenLeaves:165,firstHaltLeaves,counts,masses,refined};
const content=JSON.stringify(out,null,2)+"\n";
const path=resolve(here,"one-step-refine.json");
if(process.argv.includes("--write"))writeFileSync(path,content);
else assert.equal(readFileSync(path,"utf8"),content,"Stale refinement manifest");
console.log(JSON.stringify({counts,masses}));
