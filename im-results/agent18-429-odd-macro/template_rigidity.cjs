#!/usr/bin/env node
"use strict";
// Reproduce exact symbolic coefficient formulas and entire strict runs for
// the k=56 and k=89 near-power binary halfstep templates.
// Node.js standard library only; all arithmetic uses BigInt.
const assert = require("assert").strict;
const cases = [
 {name:"a=2, k=56",a:2n,b:2n,k:56,u:"101100000",v:"1011111111",
  z:"0010100101",t:10,C:843n,p0const:-6n,wT:162n,wConst:-843n,
  Q:648n,eT:26n,eK:39n,eConst:-2184n},
 {name:"a=1, k=89",a:1n,b:0n,k:89,u:"1110",v:"11111",
  z:"00011110",t:8,C:14n,p0const:-8n,wT:21n,wConst:-14n,
  Q:84n,eT:1n,eK:3n,eConst:-267n}
];
const pow=(n)=>4n**BigInt(n);
const len=(phase,bit)=>bit?(phase?3n:9n):(phase?1n:5n);
const off=(phase,bit)=>bit?(phase?4n:12n):0n;
function coeff(T=0n,k=0n,C=0n,q=0n){return {T,k,C,q};}
function cost(word,phase) {
 let sum=0n;
 for(const bit of word){sum+=len(phase,bit==="1");phase^=1;}
 return sum;
}
// Height returned as (T*x.T+k*x.k+C*x.C+x.q)/den; rank as coefficient row.
function symbolic(word,phase,p,y){
 p={...p};y={...y};let den=1n;
 for(const ch of word){
  const bit=ch==="1",dt=len(phase,bit),of=off(phase,bit);
  for(const f of ["T","k","C","q"])
    y[f]+=bit?p[f]*den:0n;
  y.q+=of*den;
  p.q+=dt;den*=4n;phase^=1;
 }
 return {p,y,den};
}
function run(word,p,y){
 for(let i=0;i<word.length;i++){
  const phase=Number(p&1n), bit=word[i]==="1";
  const numerator=y+(bit?p:0n)+off(phase,bit);
  assert.equal(numerator%4n,0n,"nonintegral step "+i);
  p+=len(phase,bit);y=numerator/4n;
  assert.ok(y>0n&&3n*y<p,"non-strict cone "+i);
 }
 return [p,y];
}
for(const x of cases){
 const {a,b,k,u,v,z,t,C}=x,r=u.length,s=v.length,K=BigInt(k),T=pow(k);
 const phaseCross=Number(b&1n);
 const phaseU=phaseCross^(r%2);
 const fu=symbolic(u,phaseU,coeff(a,0n,0n,b-cost(u,phaseU)),coeff(0n,0n,1n,0n));
 assert.equal(fu.y.T,x.wT);assert.equal(fu.y.q,x.wConst);
 assert.equal(fu.y.C,1n);assert.equal(fu.den,pow(r));
 assert.equal(-fu.y.q,C);
 const qNum=fu.y.T*pow(s),qDen=pow(r);
 assert.equal(qNum%qDen,0n);
 const Q=qNum/qDen;assert.equal(Q,x.Q);
 const par=(k+s)%2,eps=par?(phaseCross?-2n:2n):0n;
 const gamma=b-3n*BigInt(s)+eps;
 const fv=symbolic(v,phaseCross^par,coeff(a,3n,0n,gamma),coeff(0n,0n,0n,Q));
 const e=coeff();
 for(const f of ["T","k","C","q"])e[f]=fv.den*fv.p[f]-3n*fv.y[f];
 assert.equal(e.T,x.eT);assert.equal(e.k,x.eK);
 assert.equal(e.q,x.eConst);assert.equal(e.C,0n);
 let D=0n;for(let i=0;i<v.length;i++)if(v[i]==="1")D+=pow(i);
 const c=pow(s)-3n*D;
 assert.ok(c>=1n);assert.equal(e.T,a*c);assert.equal(e.k,3n*c);
 assert.equal((-e.q)%e.k,0n);assert.equal((-e.q)/e.k,K);
 const zero1="0".repeat(k-r),zero2="0".repeat(k-s);
 const startPhase=phaseCross^(k%2);
 const p0=a*T+b-cost(zero1+u,startPhase);
 const y0=C*pow(k-r);
 assert.equal(p0,a*T-3n*K+x.p0const);
 assert.ok(y0>0n&&3n*y0<p0);
 const first=run(zero1+u,p0,y0);
 assert.equal(first[0],a*T+b);
 const second=run(zero2+v,...first);
 const deficit=second[0]-3n*second[1];
 assert.equal(pow(s)*deficit,e.T*T+e.k*K+e.q);
 const last=run("1".repeat(k-t)+z,...second);
 console.log(JSON.stringify({template:x.name,unique_scale:k,
  initial_rank:String(p0), initial_height:String(y0), first_tail:{
    power_coefficient:String(fu.y.T),initial_height_coeff:String(fu.y.C),
    constant:String(fu.y.q),denominator:String(fu.den)},
  second_tail_deficit:{power_coefficient:String(e.T),
    rank_linear_coefficient:String(e.k),constant:String(e.q),
    denominator:String(fv.den)}, nonzero_drift_c:String(c),
  final_rank:String(last[0])},null,2));
}
console.log("Exact symbolic coefficients and both entire crossing words verified.");