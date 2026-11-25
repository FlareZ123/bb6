#!/usr/bin/env node
// Reproducible heuristic sweep of the 19 ten-hole root siblings.
// This script emits candidate lasso/side-cycle witnesses only; Lean must
// independently validate them with residualWitnessOK before use in a proof.
import fs from "node:fs";
const source = process.argv[2] ?? "im-results/agent13-roster-convergence/canonical-124.json";
const data = JSON.parse(fs.readFileSync(source, "utf8"));
const roots = data.entries.filter(e => e.holes === 10);
const moves = [];
for (let q=0;q<6;q++) for (let w=0;w<2;w++) for (let r=0;r<2;r++)
  moves.push(`${w}${r?"R":"L"}${"ABCDEF"[q]}`);
function parseAct(a){return {w:Number(a[0]),dir:a[1],q:"ABCDEF".indexOf(a[2])};}
function step(tab,c){
  const slot=c.s*2+(c.ones.has(c.h)?1:0),a=tab[slot];
  if(a===null||a===undefined)return {kind:"hole",slot};
  if(a==="HHH")return {kind:"halt"};
  const {w,dir,q}=parseAct(a);
  if(w)c.ones.add(c.h);else c.ones.delete(c.h);
  c.h+=dir==="R"?1:-1;c.s=q;
  return {kind:"ok"};
}
function clone(c){return {s:c.s,h:c.h,ones:new Set(c.ones)};}
function key(c){return `${c.s}|${c.h}|${[...c.ones].sort((a,b)=>a-b).join(",")}`;}
function run(tab,start,n){
  let c=clone(start),history=[clone(c)];
  for(let i=0;i<n;i++){const z=step(tab,c);if(z.kind!=="ok")return {kind:z.kind,step:i,slot:z.slot,history,config:c};history.push(clone(c));}
  return {kind:"ok",config:c,history};
}
function lasso(tab,cap=80){
  const c={s:0,h:0,ones:new Set()},seen=new Map([[key(c),0]]);
  for(let n=1;n<=cap;n++){const z=step(tab,c);if(z.kind!=="ok")return null;const k=key(c);if(seen.has(k))return {entry:seen.get(k),period:n-seen.get(k),n};seen.set(k,n);}
  return null;
}
function sideCycle(tab,entryCap=6,periodCap=20,boundaryRadius=10){
  for(let entry=0;entry<=entryCap;entry++){
    const rr=run(tab,{s:0,h:0,ones:new Set()},entry);if(rr.kind!=="ok")continue;const c=rr.config;
    for(let period=1;period<=periodCap;period++){
      const pp=run(tab,c,period);if(pp.kind!=="ok")continue;const d=pp.config,delta=d.h-c.h,right=delta>=0;
      if(d.s!==c.s || (right&&delta<0) || (!right&&delta>0))continue;
      for(let radius=0;radius<=boundaryRadius;radius++){
        const boundary=right?c.h-radius:c.h+radius,onSide=x=>right?x>=boundary:x<=boundary;
        if(!onSide(c.h)||!pp.history.slice(0,period).every(q=>onSide(q.h)))continue;
        let ok=true;
        for(const x of c.ones)if(onSide(x)&&!d.ones.has(x+delta)){ok=false;break;}
        if(!ok)continue;
        for(const y of d.ones)if(onSide(y-delta)&&!c.ones.has(y-delta)){ok=false;break;}
        if(ok)return {entry,period,right,boundary,delta};
      }
    }
  }
  return null;
}
const parents=[];
for(const e of roots){
  const tab=e.table.slice(),initial=run(tab,{s:0,h:0,ones:new Set()},20);
  if(initial.kind!=="hole")throw new Error(`raw ${e.raw_residual_index}: expected first hole, got ${initial.kind}`);
  const witnesses=[],openMoves=[];
  for(const mv of moves){const t=tab.slice();t[initial.slot]=mv;const l=lasso(t,80);if(l){witnesses.push({childMove:mv,kind:"lasso",n:l.n,entry:l.entry,period:l.period});continue;}const s=sideCycle(t,6,20,10);if(s){witnesses.push({childMove:mv,kind:"side",...s});continue;}openMoves.push(mv);}
  parents.push({rawResidualIndex:e.raw_residual_index,parentMove:e.address[0].move,firstHoleSlot:`${"ABCDEF"[Math.floor(initial.slot/2)]}${initial.slot%2}`,firstHoleStep:initial.step,lassoCount:witnesses.filter(w=>w.kind==="lasso").length,sideCycleCount:witnesses.filter(w=>w.kind==="side").length,closedOrdinaryCount:witnesses.length,witnesses,openMoves});
}
const closed=parents.reduce((s,p)=>s+p.closedOrdinaryCount,0),open=parents.reduce((s,p)=>s+p.openMoves.length,0);
const out={status:"heuristic candidate roster; not a proof until every listed witness is checked by Lean residualWitnessOK",source,scope:"All 19 ten-hole root siblings in canonical-124, split at their first undefined row after the two-step known prefix",search:{lassoTotalStepCap:80,sideEntryCap:6,sidePeriodCap:20,sideBoundaryRadius:10,sideBoundarySearch:"closest boundary first; boundary on retained side of entry head"},summary:{parents:parents.length,ordinaryChildren:parents.length*24,lassoWitnesses:parents.reduce((s,p)=>s+p.lassoCount,0),sideCycleWitnesses:parents.reduce((s,p)=>s+p.sideCycleCount,0),closedOrdinary:closed,openOrdinary:open,immediateHaltBranches:parents.length,closedIncludingHalts:closed+parents.length,initialCompletionMass:`${parents.length}*25^10`,remainingCompletionMass:`${open}*25^9`,massIdentity:`${open}*25^9 + ${closed+parents.length}*25^9 = ${parents.length}*25^10`},parents};
process.stdout.write(JSON.stringify(out,null,2)+"\n");
