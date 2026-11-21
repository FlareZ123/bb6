#!/usr/bin/env node
"use strict";

// Exact reduced-map replay from the source-certified S4 state at return 5457.
// Four 327,680-return P blocks connect it to the first-level macro's blockRoot.
function assert(ok,message){if(!ok)throw new Error(message);}
function W(xs){let w=0n;for(let i=xs.length-1;i>=0;i--)w=xs[i]+1n+2n*w;return w;}
function gate(c,xs){
  const out=[];
  let a=xs.length===0?c-1n:xs[0]+c;
  let i=xs.length===0?0:1;
  while(i<xs.length&&(a&1n)===1n){
    out.push(a/2n);
    a=xs[i]+a/2n+1n;
    i++;
  }
  if((a&1n)===1n){
    while((a&1n)===1n){
      if(a<=1n)return null;
      out.push(a/2n);
      a/=2n;
    }
    if(a===0n)return null;
    out.push(a/2n+2n,a/2n-1n);
  }else if(i<xs.length){
    out.push(a/2n+2n,xs[i]+a/2n);
    for(++i;i<xs.length;i++)out.push(xs[i]);
  }else{
    if(a===0n)return null;
    out.push(a/2n+2n,a/2n-1n);
  }
  return out;
}
function factorTwo(n){let v=0;while(n%2n===0n){n/=2n;v++;}return{v,odd:n};}

function discountedQScaled(xs,bits=64){
  let q=0n;
  for(let i=0;i<xs.length;i++)q+=(xs[i]+1n)<<BigInt(bits-i);
  return q;
}
function checkFullCarryQUpdate(xs,ys,c,r,odd){
  const bits=64,scale=1n<<BigInt(bits);
  const before=discountedQScaled(xs,bits),after=discountedQScaled(ys,bits);
  const numerator=2n*c*scale-before+(odd+27n)*(1n<<BigInt(bits-r-2));
  assert(numerator%3n===0n,"discounted-Q update numerator is not divisible by three");
  const predicted=numerator/3n;
  assert(after-before===predicted,"corrected discounted-Q update mismatch");
  return {carryDepth:r,scaleBits:bits,deltaScaled:String(after-before),matches:true};
}
function momentStats(xs){
  let mass=0n,first=0n,second=0n,weighted=0n,power=1n;
  for(let i=0;i<xs.length;i++){
    const x=xs[i]+1n;
    mass+=x;
    first+=BigInt(i)*x;
    second+=BigInt(i*i)*x;
    weighted+=power*x;
    power<<=1n;
  }
  return {mass,first,second,weighted};
}
function ceilDiv(a,b){return a>=0n?(a+b-1n)/b:a/b;}
function tailMomentData(xs,k){
  const n=xs.length,L=n-k,all=momentStats(xs);
  let pm=0n,pd=0n,pe=0n,pw=0n;
  for(let i=0;i<k;i++){
    const x=xs[i]+1n;
    pm+=x;pd+=BigInt(i)*x;pe+=BigInt(i*i)*x;
    pw+=(1n<<BigInt(i))*x;
  }
  const tailMass=all.mass-pm;
  const R=tailMass-BigInt(L);
  const J=all.first-pd-BigInt(k)*tailMass-BigInt(L*(L-1)/2);
  let baseline2=0n;
  for(let j=0;j<L;j++)baseline2+=BigInt((k+j)*(k+j));
  const K=all.second-pe-baseline2-BigInt(k*k)*R-2n*BigInt(k)*J;
  return {n,L,all,pm,pd,pe,pw,R,J,K,z:xs.slice(k)};
}
function exactThreeDigitMomentTail(xs,k,c){
  const d=tailMomentData(xs,k);
  assert(d.L===3,"three-digit moment tail expected");
  assert((d.K-d.J)%2n===0n,"three-digit moment parity");
  const z2=(d.K-d.J)/2n,z1=2n*d.J-d.K,z0=d.R-z1-z2;
  assert(z0>=0n&&z1>=0n&&z2>=0n,"negative reconstructed tail");
  assert(z0===d.z[0]&&z1===d.z[1]&&z2===d.z[2],
    "three-digit moment reconstruction mismatch");
  const q=(d.all.weighted+c)/(1n<<BigInt(d.n-1));
  return {
    prefixLength:k,tailLength:3,R:String(d.R),J:String(d.J),K:String(d.K),
    reconstructedTail:[z0,z1,z2].map(String),terminalQuotient:String(q),
    powerOfTwo:false
  };
}
function fourDigitMomentInterval(xs,k,c){
  const d=tailMomentData(xs,k);
  assert(d.L===4,"four-digit moment tail expected");
  assert((d.K-d.J)%2n===0n,"four-digit moment parity");
  const A=(d.K-d.J)/2n;
  let tMin=ceilDiv(2n*A-d.J,3n);
  if(tMin<0n)tMin=0n;
  let tMax=A/3n;
  if(d.R-d.J+A<tMax)tMax=d.R-d.J+A;
  assert(tMin<=tMax,"empty four-digit moment fibre");
  const actualT=d.z[3];
  assert(actualT>=tMin&&actualT<=tMax,"actual tail outside moment fibre");
  const wzMin=d.R+d.J+A+tMin,wzMax=d.R+d.J+A+tMax;
  const base=(1n<<BigInt(k))*15n;
  const wMin=d.pw+base+(1n<<BigInt(k))*wzMin;
  const wMax=d.pw+base+(1n<<BigInt(k))*wzMax;
  const denominator=1n<<BigInt(d.n-1);
  const qMin=ceilDiv(wMin+c,denominator),qMax=(wMax+c)/denominator;
  const actualQ=(d.all.weighted+c)/denominator;
  assert(qMin<=actualQ&&actualQ<=qMax,"actual terminal quotient outside interval");
  for(let power=1n;power<=qMax;power<<=1n)
    assert(power<qMin||power>qMax,"moment interval contains a power of two");
  return {
    prefixLength:k,tailLength:4,R:String(d.R),J:String(d.J),K:String(d.K),
    A:String(A),tMin:String(tMin),tMax:String(tMax),actualT:String(actualT),
    actualTail:d.z.map(String),weightedTailMin:String(wzMin),
    weightedTailMax:String(wzMax),qMin:String(qMin),qMax:String(qMax),
    actualQuotient:String(actualQ),containsPowerOfTwo:false
  };
}
const C=[509n,290n,219n];
const BLOCK=327680;
const ROOT=[
  283n,906n,982n,3490n,3734n,5935n,13580n,109210n,171050n,
  366446n,435688n,443554n,1702180n,1770018n,211301n,281569n,35137n,35134n
];
const EXPECTED=[
  283n,906n,982n,3490n,3734n,5935n,13580n,109210n,171050n,
  366446n,435438n,366335n,527037n,2639156n,3037351n,3252483n,
  6310511n,24221543n,24423525n,56750562n,67602890n,162126013n,
  335820941n,659578070n
];
let state=ROOT.slice();
const events=[];
for(let r=0;r<4*BLOCK;r++){
  for(let j=0;j<3;j++){
    const c=C[j],beforeLength=state.length;
    const potential=W(state)+c;
    const next=gate(c,state);
    assert(next!==null,`halt at relative return ${r}, stage ${j}`);
    if(next.length>beforeLength){
      const denominator=1n<<BigInt(beforeLength-1);
      assert(potential%denominator===0n,"full-suffix potential not divisible");
      const q=potential/denominator;
      const f=factorTwo(q);
      assert(f.odd!==1n,"a full-suffix event was a power-of-two halt");
      const carryDepth=beforeLength-1+f.v;
      const discountedQUpdate=checkFullCarryQUpdate(state,next,c,carryDepth,f.odd);
      const momentCertificate=beforeLength===18
        ? exactThreeDigitMomentTail(state,15,c)
        : beforeLength===22
          ? fourDigitMomentInterval(state,18,c)
          : null;
      events.push({
        relativeReturn:r,stage:j,offset:String(c),oldLength:beforeLength,
        newLength:next.length,W:String(W(state)),potential:String(potential),
        terminalQuotient:String(q),v2:Number(f.v),oddPart:String(f.odd),
        quotientMod31:String(q%31n),discountedQUpdate,momentCertificate
      });
    }
    state=next;
  }
}
assert(events.length===2,"unexpected full-suffix event count");
assert(state.length===EXPECTED.length&&state.every((x,i)=>x===EXPECTED[i]),
  "the replay did not reach the expected blockRoot");
assert(events[0].relativeReturn===25685&&events[0].stage===2&&
  events[0].terminalQuotient==="6578056"&&events[0].oddPart==="822257",
  "first full-suffix event changed");
assert(events[1].relativeReturn===929375&&events[1].stage===1&&
  events[1].terminalQuotient==="283561618"&&events[1].oddPart==="141780809",
  "second full-suffix event changed");
assert(events[0].momentCertificate.terminalQuotient==="6578056"&&
  events[0].momentCertificate.reconstructedTail.join(",")==="13047686,3611172,35134",
  "first event moment reconstruction changed");
assert(events[1].momentCertificate.qMin==="283510228"&&
  events[1].momentCertificate.qMax==="296203294"&&
  events[1].momentCertificate.actualQuotient==="283561618",
  "second event moment interval changed");
assert(events[0].discountedQUpdate.carryDepth===20&&
  events[1].discountedQUpdate.carryDepth===22&&
  events.every(e=>e.discountedQUpdate.matches),
  "corrected discounted-Q identity changed");
console.log(JSON.stringify({
  sourceCertifiedStartReturn:5457,
  reducedPReturns:4*BLOCK,
  finalReturn:5457+4*BLOCK,
  GApplications:4*BLOCK*3,
  fullSuffixEvents:events,
  finalLength:state.length,
  blockRoot:state.map(String),
  matchesExpectedBlockRoot:true,
  evidence:"deterministic BigInt reduced-map replay; not a Lean-kernel proof"
},null,2));
