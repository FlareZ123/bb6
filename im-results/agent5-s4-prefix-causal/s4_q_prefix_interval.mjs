#!/usr/bin/env node
"use strict";

// Finite root propagation of the corrected discounted-Q recurrence.
// Starts from the source-certified 18-digit state at reduced P-return 5457
// and stops immediately before G(290) at relative return 929375.
// This is a finite interval diagnostic, not an all-time root invariant.

function assert(ok,message){if(!ok)throw new Error(message);}
const K=64,k=18,targetReturn=929375;
const SCALE=1n<<BigInt(K);
const seed=[283,906,982,3490,3734,5935,13580,109210,171050,
  366446,435688,443554,1702180,1770018,211301,281569,35137,35134];
const offsets=[509,290,219];

function prefixGate(p,c){
  const out=[];
  let h=p[0]+c;
  for(let i=1;i<p.length;i++){
    const d=p[i];
    if(h%2===0){
      const q=h/2;
      out.push(q+2,d+q,...p.slice(i+1));
      return out;
    }
    const q=Math.floor(h/2);
    out.push(q);
    h=d+q+1;
  }
  out.push(h%2===0?h/2+2:Math.floor(h/2));
  assert(out.every(Number.isSafeInteger),"prefix coefficient exceeded safe integer range");
  return out;
}
function weightPrefixPlusOffset(p,c){
  let w=c,power=1;
  for(let i=0;i<p.length;i++){
    w+=(p[i]+1)*power;
    power*=2;
  }
  assert(Number.isSafeInteger(w),"prefix weighted sum exceeded safe integer range");
  return w;
}
function v2(n){
  let r=0;
  while(n%2===0){n/=2;r++;}
  return r;
}
function qScaled(p){
  let q=0n;
  for(let i=0;i<p.length;i++)
    q+=(BigInt(p[i]+1)<<BigInt(K-i));
  return q;
}
function shallowDeltaScaled(p,c,r){
  let prefix=0n;
  for(let i=0;i<=r;i++)
    prefix+=(BigInt(p[i]+1)<<BigInt(K-i));
  let t=BigInt(p[0]+1+c);
  for(let i=1;i<=r;i++)
    t=BigInt(p[i]+1)+t/2n;
  const numerator=2n*BigInt(c)*SCALE-prefix+
    (t+27n)*(1n<<BigInt(K-r-2));
  assert(numerator%3n===0n,"shallow Q update failed exact divisibility");
  return numerator/3n;
}
function ceilDiv(a,b){return (a+b-1n)/b;}
function floorDiv(a,b){return a/b;}

let p=seed.slice();
let mass=5590215n;
let lo=qScaled(p),hi=lo;
let deep=0,shallow=0,processed=0;
let snapshot=null;

outer:
for(let ret=0;ret<=targetReturn;ret++){
  for(let j=0;j<3;j++){
    if(ret===targetReturn&&j===1){
      snapshot={prefix:p.slice(),mass,lo,hi,deep,shallow,processed};
      break outer;
    }
    const c=offsets[j];
    const rPrefix=v2(weightPrefixPlusOffset(p,c));
    if(rPrefix<k){
      const delta=shallowDeltaScaled(p,c,rPrefix);
      const factor=3n**BigInt(deep);
      lo+=delta*factor;
      hi+=delta*factor;
      shallow++;
    }else{
      // For the actual carry depth r>=k:
      // Q'=(2/3)Q+(2/3)c+eta,
      // 0<=eta<=(3M+c+27)/(3*2^(k+2)).
      const oldDenominator=SCALE*(3n**BigInt(deep));
      const errorNumerator=(3n*mass+BigInt(c)+27n)*oldDenominator/
        (1n<<BigInt(k+2));
      lo=2n*lo+2n*BigInt(c)*oldDenominator;
      hi=2n*hi+2n*BigInt(c)*oldDenominator+errorNumerator;
      deep++;
    }
    mass+=BigInt(c+2);
    p=prefixGate(p,c);
    processed++;
  }
}
assert(snapshot!==null,"target event was not reached");
assert(snapshot.mass===957270726n&&snapshot.deep===11&&
  snapshot.shallow===2788115&&snapshot.processed===2788126,
  "finite prefix path summary changed");
const expectedPrefix=[397,907,1339,6000,7805,6594,37229,17305,92604,
  124823,266861,853858,2288581,4369053,4153893,7504114,34613718,92749679];
assert(snapshot.prefix.every((x,i)=>x===expectedPrefix[i]),
  "18-prefix at target event changed");

const denominator=SCALE*(3n**BigInt(snapshot.deep));
const prefixMass= snapshot.prefix.reduce((s,d)=>s+BigInt(d+1),0n);
const prefixWeighted=snapshot.prefix.reduce(
  (s,d,i)=>s+((BigInt(d+1))<<BigInt(i)),0n);
const prefixQNumerator=snapshot.prefix.reduce(
  (s,d,i)=>s+((BigInt(d+1))<<BigInt(17-i)),0n);
const tailExcessMass=snapshot.mass-prefixMass-4n;
assert(tailExcessMass===810175944n,"tail excess mass changed");

// Q0 = 2^18*(Q - Q_prefix) - (1+1/2+1/4+1/8).
// Use denominator 8*denominator and outward-round to integers.
const q0Denominator=8n*denominator;
const q0LoNumerator=(1n<<21n)*snapshot.lo-
  16n*prefixQNumerator*denominator-15n*denominator;
const q0HiNumerator=(1n<<21n)*snapshot.hi-
  16n*prefixQNumerator*denominator-15n*denominator;
const q0Lower=floorDiv(q0LoNumerator,q0Denominator);
const q0Upper=ceilDiv(q0HiNumerator,q0Denominator);
assert(q0Lower===175849077n&&q0Upper===702151658n,
  "outward-rounded discounted tail interval changed");

// Cauchy-Schwarz and the endpoint chord for 2^j on j=0..3.
const wzLower=ceilDiv(tailExcessMass*tailExcessMass,q0Upper);
const wzUpper=tailExcessMass+8n*(tailExcessMass-q0Lower);
const qLower=ceilDiv(prefixWeighted+290n+
  (1n<<18n)*(15n+wzLower),1n<<21n);
const qUpper=floorDiv(prefixWeighted+290n+
  (1n<<18n)*(15n+wzUpper),1n<<21n);
assert(qLower===123903222n&&qUpper===742649644n,
  "terminal quotient interval changed");
const powers=[1n<<27n,1n<<28n,1n<<29n];
assert(powers.every(x=>qLower<=x&&x<=qUpper),
  "expected powers of two no longer lie in the interval");

console.log(JSON.stringify({
  target:"before G(290), relative P-return 929375",
  prefix:snapshot.prefix,
  mass:String(snapshot.mass),
  prefixCrossingGates:snapshot.deep,
  prefixStoppingGates:snapshot.shallow,
  processedGates:snapshot.processed,
  QIntervalNumerator:[String(snapshot.lo),String(snapshot.hi)],
  QIntervalDenominator:String(denominator),
  tailExcessMass:String(tailExcessMass),
  Q0OutwardIntegerInterval:[String(q0Lower),String(q0Upper)],
  weightedTailInterval:[String(wzLower),String(wzUpper)],
  terminalQuotientInterval:[String(qLower),String(qUpper)],
  containedPowersOfTwo:powers.map(String),
  conclusion:"The corrected 18-prefix Q interval is too coarse to exclude the candidate powers."
},null,2));
