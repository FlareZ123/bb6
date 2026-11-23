"use strict";
/*
  Exhaustive bounded five-primitive-move blank-to-translated-blank source
  family, six ordinary control states, two symbols, two-sided tape.
  Enumerates ALL 32 direction words * ALL 32 write words * ALL 6^4
  intermediate control-state words; no sampling or heuristic search.
  One distinct fixed table per successful trace with FIVE distinct
  physically consulted (state,read-bit) input rows.
  The five-step nonhalting proof is exact complete-tape translation
  invariance and applies to every choice of the 7 unrestricted rows.

  Node.js >=16. Use first-difference/unique-physical-prefix argument for
  global pairwise disjointness (does not require 870m explicit pair tests).
*/
const assert=require("node:assert/strict");
const slot=(s,b)=>2*s+b;
const action=(w,d,to)=>({w,d,to});
function signature(p){return [...p].sort((a,b)=>a[0]-b[0]).map(
  ([s,a])=>[s,a.w,a.d,a.to].join(":")).join("|");}
function simulate(p){
  let state=0,head=0;const marked=new Set(),consulted=[];
  for(let t=0;t<5;t++){
    const read=+marked.has(head),key=slot(state,read);
    consulted.push(key);
    const a=p.get(key);assert(a,"unassigned physically consulted input");
    if(a.w)marked.add(head);else marked.delete(head);
    head+=a.d;state=a.to;
  }
  assert.equal(state,0);
  assert.notEqual(head,0);
  assert.equal(marked.size,0);
  assert.equal(new Set(consulted).size,5);
  return {head,consulted};
}

const keys=new Set();
const displacementCount={};
const templateCountByDisplacement={};
let templates=0,attemptedStateWords=0,accepted=0,templatesWithWitness=0;
for(let moveMask=0;moveMask<32;moveMask++){
  const dirs=Array.from({length:5},(_,i)=>(moveMask&(1<<i))?1:-1);
  const heads=[0];
  for(const d of dirs)heads.push(heads[heads.length-1]+d);
  assert.notEqual(heads[5],0,"odd-length walk cannot have zero displacement");
  for(let writeMask=0;writeMask<32;writeMask++){
    const writes=Array.from({length:5},(_,i)=>(writeMask&(1<<i))?1:0);
    const marked=new Set(),reads=[];
    for(let i=0;i<5;i++){
      const h=heads[i];reads.push(+marked.has(h));
      if(writes[i])marked.add(h);else marked.delete(h);
    }
    if(marked.size!==0)continue;
    templates++;
    templateCountByDisplacement[heads[5]]=
      (templateCountByDisplacement[heads[5]]||0)+1;
    let foundForTemplate=0;
    for(let q1=0;q1<6;q1++)for(let q2=0;q2<6;q2++)
    for(let q3=0;q3<6;q3++)for(let q4=0;q4<6;q4++){
      attemptedStateWords++;
      const states=[0,q1,q2,q3,q4,0];
      const consulted=states.slice(0,5).map((s,i)=>slot(s,reads[i]));
      if(new Set(consulted).size!==5)continue;
      const p=new Map();
      for(let i=0;i<5;i++){
        const key=consulted[i];
        assert(!p.has(key));
        p.set(key,action(writes[i],dirs[i],states[i+1]));
      }
      assert.equal(p.size,5);
      const sig=signature(p);
      assert(!keys.has(sig),"duplicate five-row partial table");
      keys.add(sig);
      const trace=simulate(p);
      assert.equal(trace.head,heads[5]);
      assert.deepEqual(trace.consulted,consulted);
      accepted++;foundForTemplate++;
      displacementCount[heads[5]]=(displacementCount[heads[5]]||0)+1;
    }
    if(foundForTemplate)templatesWithWitness++;
  }
}
assert.equal(templates,116);
assert.equal(accepted,41760);
assert.equal(keys.size,accepted);
assert.deepEqual(displacementCount,{
  "1":16800,"3":3960,"5":120,"-1":16800,"-3":3960,"-5":120
});

/* The earlier 1,200-cylinder five-slot family is a strict subfamily. */
let originalFamily=0;
for(const d of [-1,1])for(let b=1;b<6;b++)
for(let c=0;c<6;c++)for(let z=0;z<6;z++){if(z===c)continue;
  for(let e=0;e<6;e++){if(e===0||e===b)continue;
    const p=new Map([[slot(0,0),action(1,d,b)],
      [slot(b,0),action(1,-d,c)],[slot(c,1),action(0,d,z)],
      [slot(z,1),action(0,-d,e)],[slot(e,0),action(0,d,0)]]);
    assert.equal(p.size,5);
    assert(keys.has(signature(p)),"earlier certified source member missing");
    originalFamily++;
  }
}
assert.equal(originalFamily,1200);

const mass=BigInt(accepted)*25n**7n;
const universe=25n**12n;
assert.equal(mass,254882812500000n);
assert.equal(universe,59604644775390625n);
console.log(JSON.stringify({
  directionWords:32,writeWords:32,returnBlankGeometricTemplates:templates,
  templatesWithFiveDistinctInputWitness:templatesWithWitness,
  enumeratedIntermediateStateWords:attemptedStateWords,
  uniqueFiveRowCylinders:accepted,
  disjointnessArgument:"first differing physical instruction in deterministic blank-start trace",
  displacementCount,
  templateCountByDisplacement,
  earlierFiveStepSubfamily:originalFamily,
  fixedRows:5,freeRows:7,
  exactCompletionUnionMass:mass.toString(),
  allRawTables:universe.toString(),
  exactFraction:"41760/9765625",
  percentage:0.4276224
},null,2));
