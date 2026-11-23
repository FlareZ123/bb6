"use strict";
/*
  Full four-slot convoy family, exact tape simulation and old-oracle
  computational preflight. The oracle is a source-shaped JavaScript
  implementation, NOT a substitute for Lean original-source acceptance.
  Expected: 300 pairwise-disjoint translated-pair cylinders, all 300 open
  in original depth-four lasso audit; all 44,850 pair conflicts; 300*25^8.
*/
const assert=require("node:assert/strict");
const slot=(s,b)=>2*s+b, A=(w,d,to)=>({w,d,to});
const blank=(s=0)=>({s,h:0,ones:new Set()});
function step(p,c){if(!c)return null;const a=p.get(slot(c.s,+c.ones.has(c.h)));
  if(!a)return null;const ones=new Set(c.ones);
  if(a.w)ones.add(c.h);else ones.delete(c.h);
  return {s:a.to,h:c.h+a.d,ones};
}
function run(p,c,n){for(let i=0;i<n;i++){c=step(p,c);if(!c)return null;}return c;}
function eq(a,b){return !!a&&!!b&&a.s===b.s&&a.h===b.h&&
  a.ones.size===b.ones.size&&[...a.ones].every(x=>b.ones.has(x));}
function fresh(c,d){return [...c.ones].every(x=>d===1?x<c.h:x>c.h);}
function ray(p){
  for(let k=0;k<=6;k++){const c=run(p,blank(),k);if(!c)continue;
    for(let mask=1;mask<64;mask++){if(!(mask&(1<<c.s)))continue;
      for(const d of [-1,1]){if(!fresh(c,d))continue;let ok=true;
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
function zero(p){
  for(let mask=1;mask<64;mask++){if(!(mask&1))continue;let ok=true;
    for(let s=0;s<6;s++)if(mask&(1<<s)){
      const a=p.get(slot(s,0));
      if(!a||a.w!==0||!(mask&(1<<a.to)))ok=false;
    }
    if(ok)return true;
  }
  return false;
}
function lasso(p){const cs=[blank()];for(let i=1;i<=12;i++){
  const c=step(p,cs[cs.length-1]);if(!c)break;
  if(cs.some(d=>eq(c,d)))return true;cs.push(c);
}return false;}
function entry(p){
  for(let k=0;k<2;k++){const e=run(p,blank(),k);if(!e)continue;
    for(let n=1;n<=4;n++){let c=blank(e.s);const cs=[];
      for(let j=0;j<n;j++){cs.push(c);c=step(p,c);if(!c)break}
      if(!c)continue;
      for(const d of [-1,1])
        if(fresh(e,d)&&c.s===e.s&&c.h*d>0&&fresh(c,d)&&
          cs.every(v=>v.h*d>=0))return true;
    }
  }
  return false;
}
function old(p){return zero(p)||ray(p)||lasso(p)||entry(p);}
function first(p){let c=blank();for(let i=0;i<12;i++){
  const key=slot(c.s,+c.ones.has(c.h));
  if(!p.has(key))return key;c=step(p,c);if(!c)return null;
}return null;}
function table(d,B,C,D){assert(B!==0 && C!==D);
  const p=new Map([[slot(0,0),A(1,d,B)],[slot(B,0),A(1,-d,C)],
    [slot(C,1),A(0,d,D)],[slot(D,1),A(1,d,B)]]);
  assert.equal(p.size,4);return p;
}
function conflicting(p,q){for(const [key,a] of p){
  const b=q.get(key);
  if(b&&(a.w!==b.w||a.d!==b.d||a.to!==b.to))return true;
}return false;}
const sources=[];
for(const d of [-1,1])for(let B=1;B<=5;B++)
for(let C=0;C<6;C++)for(let D=0;D<6;D++){if(C===D)continue;
  const p=table(d,B,C,D),order=[slot(0,0),slot(B,0),slot(C,1),slot(D,1)];
  let q=new Map();
  for(const key of order){assert.equal(first(q),key);
    assert.equal(old(q),false,"old oracle accepts proper parent");
    q.set(key,p.get(key));
  }
  assert.equal(old(q),false,"old oracle accepts complete four-slot table");
  assert.equal(first(q),null,"twelve-step scan still has a missing row");
  const start=run(p,blank(),2),end=run(p,start,3);
  assert(start && end && start.s===C && start.h===0&&start.ones.size===2);
  assert(end.s===C && end.h===d && end.ones.size===2);
  for(const x of start.ones)assert(end.ones.has(x+d));
  sources.push(p);
}
assert.equal(sources.length,300);
let conflicts=0;
for(let i=0;i<sources.length;i++)for(let j=i+1;j<sources.length;j++){
  assert(conflicting(sources[i],sources[j]));
  conflicts++;
}
assert.equal(conflicts,44850);
const mass=300n*25n**8n;
assert.equal(mass,45776367187500n);
const original=table(1,1,2,3);
assert.deepEqual([...original].sort((a,b)=>a[0]-b[0]),
  [...sources.find(p=>JSON.stringify([...p])===JSON.stringify([...original]))].sort((a,b)=>a[0]-b[0]));
console.log(JSON.stringify({
  acceptedByOldOracle:0,
  acceptedSourceCylinders:300,
  checkedAncestorPrefixes:1200,
  checkedDisjointPairs:conflicts,
  fixedRowsPerCylinder:4,
  freeRowsPerCylinder:8,
  exactTotalMass:mass.toString(),
  fraction:"300/390625",
  percent:0.0768,
  entryMoves:2,
  translatedPeriod:3
},null,2));
