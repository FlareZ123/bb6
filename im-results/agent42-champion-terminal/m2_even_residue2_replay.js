// Deterministic original-TM2 replay for the marker-2 n = 8q+2 reset row.
// Run with Node.js. This is regression evidence, not a proof.
"use strict";
const d0 = [0, 0, 1], d1 = [1, 1, 1];
const markerWord = m => m % 3 === 0 ? [0,1] : m % 3 === 1 ? [1,0,1] : [1,1,0,1];
const d1pow = n => Array.from({length:n}, () => d1).flat();
function binDec(len,n) {
  let p=2**(len+1)-1-n, out=[];
  for(let i=0;i<len;i++){ if(p<=1) break; out.push(...(p%2===0?d0:d1)); p=Math.floor(p/2); }
  return out;
}
const lh=[1,1,0,1,1,1];
const leftFacing=(L,n,m,a,z)=>[...binDec(a,z),...markerWord(m),...d0,...binDec(L,n),...lh];
const rightFacing=b=>[0,1,1,1,0,0,...d1pow(b+1)];
function s1Config(L,n,m,a,z,b,h) {
  const ones=new Set();
  leftFacing(L,n,m,a,z).forEach((v,i)=>{if(v)ones.add(h-i);});
  rightFacing(b).forEach((v,i)=>{if(v)ones.add(h+1+i);});
  return {state:3,head:h,ones};
}
const tm2=[
  [[1,1,1],null], [[1,-1,2],[0,1,5]], [[1,1,4],[0,-1,3]],
  [[0,-1,2],[1,1,1]], [[1,1,0],[1,1,4]], [[1,1,4],[0,1,3]]
];
function run(c,steps) {
  const ones=new Set(c.ones); let {state,head}=c;
  for(let i=0;i<steps;i++){
    const tr=tm2[state][ones.has(head)?1:0];
    if(tr===null) return null;
    const [write,dir,next]=tr;
    if(write) ones.add(head); else ones.delete(head);
    head+=dir; state=next;
  }
  return {state,head,ones};
}
function sameConfig(x,y) {
  if(!x||x.state!==y.state||x.head!==y.head||x.ones.size!==y.ones.size) return false;
  for(const p of x.ones) if(!y.ones.has(p)) return false;
  return true;
}
const failures=[]; let tested=0;
for(let q=0;q<=4;q++){
  const n=8*q+2, minL=Math.max(3,Math.ceil(Math.log2(n+1)));
  for(const L of [minL,minL+1]) for(let a=1;a<=3;a++) for(let b=0;b<=3;b++){
    const cost=6*4**b+42*2**b-9*b+35+12*a;
    const source=s1Config(L,n,2,a,0,b,0);
    const target=s1Config(L,n-1,1,a+b+2,0,2**b-1,5+3*b);
    const actual=run(source,cost); tested++;
    if(!sameConfig(actual,target)) failures.push({q,L,a,b,cost,actual:actual&&{state:actual.state,head:actual.head}});
  }
}
const report={tested,passed:tested-failures.length,failures};
if(failures.length){console.error(JSON.stringify(report,null,2));process.exitCode=1;}
else console.log(JSON.stringify(report));
