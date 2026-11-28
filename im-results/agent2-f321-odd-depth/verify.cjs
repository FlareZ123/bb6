#!/usr/bin/env node
'use strict';
// F321 source-counter inverse-ray certificate checker.
// Independent exact BigInt replay of the parameterized proof in
// results/2026-11-28-f321-odd-depth-base-four-rays-agent2.md.
// Finite samples check the algebraic proof but do not replace induction.

function assert(x,msg){if(!x)throw new Error(msg)}
function next(a,d) {
  if(a>=d+2n)return [a-d-2n,2n*d+3n];
  if(a===d+1n)return null; // halt gate
  if(a===d)return [2n*a+4n,1n];
  if(d>=3n*a+1n)return [4n*a+6n,d-3n*a];
  return [4n*a+6n,(d-a)%2n===0n?2n:1n];
}
function same([a,b],[c,d]){return a===c&&b===d}
function preds(A,D) {
  // All possible predecessors have the following complete source-map
  // classification. The middle branch is a finite interval; here every
  // checked output has D>=3, so only high and far can contribute.
  assert(D>=3n,'test only large-D outputs');
  const ps=[];
  if(D%2n===1n)ps.push({kind:'H',a:A+(D+1n)/2n,d:(D-3n)/2n});
  if(A>=6n && A%4n===2n){
    const a=(A-6n)/4n;
    ps.push({kind:'F',a,d:D+3n*a});
  }
  for(const p of ps)assert(same(next(p.a,p.d),[A,D]),'invalid inverse');
  return ps;
}
function mustUnique(A,D,kind) {
  const ps=preds(A,D);
  assert(ps.length===1 && ps[0].kind===kind,'inverse not unique at '+A+','+D);
  return [ps[0].a,ps[0].d];
}
function run(t,m){
  assert(t>=1 && t%2===1);
  const T=BigInt(t),M=BigInt(m);
  let kt=4n*M+1n,k0=kt;
  for(let j=0;j<t;j++) k0=4n*k0+2n;
  const d=8n*k0+3n;
  const r=(40n*(4n**T)-7n)/3n,mod=32n*(4n**T);
  assert((40n*(4n**T)-7n)%3n===0n,'nonintegral residue');
  assert(d%mod===r,'residue mismatch');
  let A=d+1n,D=d;
  [A,D]=mustUnique(A,D,'H');
  [A,D]=mustUnique(A,D,'F');
  let c=13n,b=0n,ki=k0;
  assert(same([A,D],[3n*ki,c*ki+b]),'Q0 mismatch');
  for(let i=0;i<t;i++){
    assert(ki%4n===2n,'wrong low base-four digit');
    [A,D]=mustUnique(A,D,'F');
    ki=(ki-2n)/4n;
    [c,b]=[4n*c+9n,b+2n*c];
    assert(same([A,D],[3n*ki,c*ki+b]),'Qi recurrence failure');
    assert(c%4n===1n && b%4n===2n*BigInt((i+1)%2),'mod-4 recurrence failure');
  }
  assert(ki===kt && kt%4n===1n,'wrong terminal digit');
  assert(A%2n===1n && D%4n===3n,'wrong penultimate parity');
  [A,D]=mustUnique(A,D,'H');
  assert(A%2n===1n && D%2n===0n,'not dead odd/even');
  assert(preds(A,D).length===0,'dead ancestor has an incoming move');
  assert(!same([A,D],[1n,1n]),'dead ancestor equals seed');
  return {t,m:String(m),d:String(d),dead:[String(A),String(D)],distance:t+3};
}
const limit=Number(process.argv[2]||'101');
assert(Number.isInteger(limit)&&limit>=1&&limit<=10000,'invalid number of m samples');
let tests=0,last;
for(let t=1;t<=15;t+=2){
  for(let m=0;m<limit;m++){last=run(t,m);tests++;}
}
console.log(JSON.stringify({status:'passed',testedInstances:tests,tOddMax:15,mCount:limit,
  t1m0:run(1,0),t3m0:run(3,0),t5m0:run(5,0),
  last},null,2));
