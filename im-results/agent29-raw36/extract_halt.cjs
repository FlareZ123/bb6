#!/usr/bin/env node
"use strict";
/* Reconstruct one literal six-state halter from a corrected candidate tree,
   independently execute its *blank-start* transition table, and report its
   exact raw step count. Distinguish the classifier's conservative +6 score.
   This is computational evidence; a Lean HaltsAfter certificate is separate.
*/
const fs=require("fs");
const {makeSearch}=require("./search.cjs");
const spec=JSON.parse(fs.readFileSync(__dirname+"/candidate.json","utf8"));
const child=+(process.argv[2]||22),wanted=+(process.argv[3]||1022);
const s=makeSearch(spec.codes,spec.options);
const root=s.parse(spec.parent);root[spec.query[2]]=child;
const result=s.run(root,true);
let answer=null;
function visit(t,p){
  if(t[0]==="last" && t[1]+6===wanted){
    answer={table:s.show(p),code:p.slice(),last:{n:t[1],slot:t[2]},weightedScore:t[1]+6};
    return true;
  }
  if(t[0]==="split"){
    const slot=t[2];
    for(let code=0;code<24;code++){
      p[slot]=code;
      if(visit(t[3][code],p))return true;
    }
    p[slot]=-1;
  }
  return false;
}
if(!visit(result.tree,root))throw Error("no explicit last-hole halt witness at "+wanted);
function runBlank(p,limit){
  const tape=new Map(), trail=[];
  let state=0,head=0;
  for(let n=0;n<=limit;n++){
    const old=tape.get(head)||0,slot=2*state+old,action=p[slot];
    if(action===-1)return {haltsAfter:n,undefinedSlot:slot,head,state,visited:trail.length,trailTail:trail.slice(-12)};
    if(action===undefined)throw Error("undefined code");
    const bit=action>=12?1:0,right=(action%12)>=6,next=action%6;
    if(n<16||n>limit-16)trail.push({n,state,head,read:old,write:bit,right,next});
    if(bit===0)tape.delete(head);else tape.set(head,1);
    head+=right?1:-1;state=next;
  }
  return {status:"did-not-halt-within-limit"};
}
answer.simulation=runBlank(answer.code,Math.max(wanted,2000));
if(answer.simulation.haltsAfter!==answer.last.n)
  throw Error("classifier/direct-simulator disagreement: "+JSON.stringify(answer));
console.log(JSON.stringify(answer,null,2));
if(process.argv[4])fs.writeFileSync(process.argv[4],JSON.stringify(answer,null,2)+"\n");
