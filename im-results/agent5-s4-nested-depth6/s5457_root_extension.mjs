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
      events.push({
        relativeReturn:r,stage:j,offset:String(c),oldLength:beforeLength,
        newLength:next.length,W:String(W(state)),potential:String(potential),
        terminalQuotient:String(q),v2:Number(f.v),oddPart:String(f.odd),
        quotientMod31:String(q%31n)
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
