"use strict";

/*
  Independent source-shaped mirror of the depth-four global lasso audit
  from LassoTraceAudit.lean + the exact finite oracles used by
  search_three_slot_translated.js (Agent 27).

  Checks for each of the 1200 five-step translated-blank cylinders:
  - old lassoDecisionOracle false at all five assigned prefixes
    AND the complete five-row table;
  - firstUnknownPhysical visits A0,B0,C1,D1,E0 in that order;
  - fifth-row table has no unknown in the 12-step bounded scan;
  - nonhalting cycle is physically shifted blank after five moves;
  - disjointness from Agent 27's 80 three-slot tables and five-slot
    two-marker source leaf.
  Also tests a nearby 300-member four-row family as a negative control:
  the old entry-macro oracle already recognizes all 300.

  This is a computational preflight, not a Lean kernel check.
*/
const assert = require("node:assert/strict");
const slot = (s, b) => s * 2 + b;
const A = (w, d, to) => ({w, d, to});
const blank = (s=0) => ({s,h:0,ones:new Set()});
function move(p,c){
  if(c===null)return null;
  const key=slot(c.s,+c.ones.has(c.h)),a=p.get(key);
  if(!a)return null;
  const ones=new Set(c.ones);
  if(a.w)ones.add(c.h);else ones.delete(c.h);
  return {s:a.to,h:c.h+a.d,ones};
}
function run(p,c,n){for(let i=0;i<n;i++){c=move(p,c);if(c===null)return null;}return c}
function eq(c,d){
  return c!==null && d!==null && c.s===d.s && c.h===d.h &&
    c.ones.size===d.ones.size && [...c.ones].every(x=>d.ones.has(x));
}
function fresh(c,d){return [...c.ones].every(x=>d===1?x<c.h:x>c.h)}
function finiteRay(p){
  for(let n=0;n<=6;n++){const c=run(p,blank(),n);if(!c)continue;
    for(let mask=1;mask<64;mask++){if(!(mask&(1<<c.s)))continue;
      for(const d of [-1,1]){if(!fresh(c,d))continue;
        let ok=true;
        for(let s=0;s<6;s++)if(mask&(1<<s)){
          const a=p.get(slot(s,0));
          if(!a||a.d!==d||!(mask&(1<<a.to)))ok=false;
        }
        if(ok)return true;
      }
    }
  }
  return false;
}
function zeroMask(p){
  for(let mask=1;mask<64;mask++){if(!(mask&1))continue;
    let ok=true;
    for(let s=0;s<6;s++)if(mask&(1<<s)){
      const a=p.get(slot(s,0));
      if(!a||a.w!==0||!(mask&(1<<a.to)))ok=false;
    }
    if(ok)return true;
  }
  return false;
}
function finiteLasso(p){
  const configs=[blank()];
  for(let n=1;n<=12;n++){
    const c=move(p,configs[configs.length-1]);
    if(c===null)break;
    for(const old of configs)if(eq(c,old))return true;
    configs.push(c);
  }
  return false;
}
function entryMacroBi(p){
  for(let entrySteps=0;entrySteps<2;entrySteps++){
    const entry=run(p,blank(),entrySteps);if(!entry)continue;
    for(let period=1;period<=4;period++){
      let c=blank(entry.s);
      const visited=[];
      for(let i=0;i<period;i++){visited.push(c);c=move(p,c);if(!c)break}
      if(!c)continue;
      for(const d of [-1,1])
        if(fresh(entry,d) && c.s===entry.s && c.h*d>0 &&
            fresh(c,d) && visited.every(x=>x.h*d>=0))return true;
    }
  }
  return false;
}
function oldOracle(p){
  // All assigned transitions are ordinary, so the separately defined
  // finiteHaltOracle cannot find an assigned halting instruction.
  return zeroMask(p)||finiteRay(p)||finiteLasso(p)||entryMacroBi(p);
}
function firstUnknown(p){
  let c=blank();
  for(let t=0;t<12;t++){
    const s=slot(c.s,+c.ones.has(c.h));
    if(!p.has(s))return s;
    c=move(p,c);
    if(!c)return null;
  }
  return null;
}
function table5(d,b,c,s,e){
  const p=new Map();
  p.set(slot(0,0), A(1,d,b));
  p.set(slot(b,0), A(1,-d,c));
  p.set(slot(c,1), A(0,d,s));
  p.set(slot(s,1), A(0,-d,e));
  p.set(slot(e,0), A(0,d,0));
  assert.equal(p.size,5);return p;
}
function table4(d,b,c,s){
  const p=new Map();
  p.set(slot(0,0), A(1,d,b));
  p.set(slot(b,0), A(1,-d,c));
  p.set(slot(c,1), A(0,d,s));
  p.set(slot(s,1), A(0,d,0));
  assert.equal(p.size,4);return p;
}
function oldThree(){
  const out=[];
  for(const d of [-1,1])for(let b=1;b<=5;b++){
    for(let c=0;c<6;c++){
      const p=new Map([[slot(0,0),A(1,d,b)],
        [slot(b,0),A(0,-d,c)],[slot(c,1),A(0,-d,0)]]);
      assert.equal(p.size,3);out.push(p);
    }
    const p4=new Map([[slot(0,0),A(1,d,b)],
      [slot(b,0),A(0,-d,0)],[slot(0,1),A(0,-d,b)]]);
    assert.equal(p4.size,3);out.push(p4);
    const pEntry=new Map([[slot(0,0),A(0,d,b)],
      [slot(b,0),A(1,-d,0)],[slot(b,1),A(0,d,b)]]);
    assert.equal(pEntry.size,3);out.push(pEntry);
  }
  assert.equal(out.length,80);return out;
}
function conflict(p,q){
  for(const [s,a] of p){const b=q.get(s);
    if(b && (a.w!==b.w || a.d!==b.d || a.to!==b.to))return true;
  }
  return false;
}
const existing5=new Map([
  [slot(0,0),A(1,1,1)],
  [slot(1,0),A(1,-1,2)],
  [slot(2,1),A(0,1,3)],
  [slot(3,1),A(1,1,4)],
  [slot(4,0),A(1,-1,2)]
]);
const old80=oldThree();
let checked5=0,checked4=0,covered4=0,oldPass5=0;
let checkedPrefixOracles=0,checkedCrossConflicts=0;
for(const d of [-1,1])for(let b=1;b<=5;b++)
for(let c=0;c<6;c++)for(let s=0;s<6;s++){if(c===s)continue;
  const p4=table4(d,b,c,s);
  checked4++;
  if(oldOracle(p4))covered4++;
  for(let e=0;e<6;e++){if(e===0||e===b)continue;
    const p=table5(d,b,c,s,e);
    checked5++;
    const order=[slot(0,0),slot(b,0),slot(c,1),slot(s,1),slot(e,0)];
    let q=new Map();
    for(const key of order){
      assert.equal(firstUnknown(q),key,"wrong physical branch order");
      assert.equal(oldOracle(q),false,"old oracle accepted an ancestor");
      checkedPrefixOracles++;
      q.set(key,p.get(key));
    }
    assert.equal(firstUnknown(q),null,"completed drift contains unknown");
    if(oldOracle(q))oldPass5++;
    assert(conflict(q,existing5),"overlaps existing five-slot cylinder");
    checkedCrossConflicts++;
    for(const other of old80){
      assert(conflict(q,other),"overlaps one of the 80 three-slot cylinders");
      checkedCrossConflicts++;
    }
    const end=run(q,blank(),5);
    assert(end && end.s===0 && end.h===d && end.ones.size===0);
  }
}
assert.equal(checked4,300);
assert.equal(covered4,300);
assert.equal(checked5,1200);
assert.equal(oldPass5,0);
assert.equal(checkedPrefixOracles,6000);
assert.equal(checkedCrossConflicts,1200*81);
console.log(JSON.stringify({
  fiveStepFamilies:checked5,
  oldOracleAcceptsFiveStep:oldPass5,
  checkedAncestorOldOracleRejections:checkedPrefixOracles,
  checkedCrossFamilyConflicts:checkedCrossConflicts,
  physicalNextRowAtDepthFour:"E/0",
  acceptedFourStepNegativeControls:covered4,
  fourStepNegativeControls:checked4,
  combinedMassIfOther81Independent:
    (7324218750000n+305181884765625n).toString()
},null,2));
