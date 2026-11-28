#!/usr/bin/env node
'use strict';
const assert=require('node:assert/strict');

// Symbolic exact-integer verifier of the all-M second-resonance construction.
// Does NOT materialize T=4^k (which has billions of bits for M>=6). Instead
// uses the proved sufficient bound T>100*k*4^(2R) and verifies every
// resulting symbolic inequality and cancellation with BigInt.
//
// Mathematical proof: LongPastUniformM.md
function check(M,s) {
  assert(Number.isSafeInteger(M)&&M>=3&&M%3===0&&M<=60);
  assert(Number.isSafeInteger(s)&&s%2===0&&s>=M+1&&s<=300);
  const E=BigInt(M%2),L=4n**BigInt(M)-1n,W=L/9n,S=BigInt(s);
  assert.equal(L%9n,0n);
  const beta=((24n-3n*BigInt(M)-2n*E)*(L/3n)-2n*BigInt(M)-E)/2n;
  const coeff=2n*L*L/9n;
  const B=coeff*4n**S-(L*S/2n)+beta;
  const R=s+2*M,top=R-1;
  const mod=(x,n)=>(x%n+n)%n;
  let rem=mod(beta-4n**BigInt(top%M),L);
  const residue=rem;
  let F=0n,nonzeroF=0,maxFExp=-1;
  for(let j=0;j<M;j++){
    const c=Number(rem%4n);rem/=4n;
    for(let u=0;u<c;u++){
      const exponent=j+u*M;
      assert(exponent<top);
      F+=4n**BigInt(exponent);nonzeroF++;
      maxFExp=Math.max(maxFExp,exponent);
    }
  }
  assert.equal(rem,0n);
  const D=4n**BigInt(top)+F;
  assert.equal(mod(D,L),mod(B,L));
  assert(D>B);
  const h=2n*(D-B)/L;
  assert(h>0n&&h%2n===0n);
  const m=3n+2n*W*4n**S;
  const k=m+1n+h,r=k-BigInt(M)-S,q=k-2n*BigInt(R)-100n*BigInt(M);
  assert(m%2n===1n&&k%2n===0n&&r>0n&&q>0n);
  assert.equal(r%2n,E);
  assert(k<4n**BigInt(R));
  assert(k>4n*BigInt(R)+100n*BigInt(M));
  assert(BigInt(R)*16n<=k);
  const delta=3n*(m+r)+3n-2n*E;
  assert(delta>12n&&delta<7n*k);
  // The initial M inverse ones start after a zero run of parity M:
  // p0=2*T-delta, y0=(2*T/3)*(1-4^(-M)).
  let phaseEven=E===0n,costSum=0n,correction=0n,K=0n;
  for(let i=0;i<M;i++){
    const cost=phaseEven?3n:9n,offset=phaseEven?4n:12n;
    costSum+=cost;
    correction=4n*correction+delta+costSum-offset;
    K=4n*K+costSum-offset;
    assert(correction>0n);
    phaseEven=!phaseEven;
  }
  assert.equal(K,-2n*BigInt(M)-E);
  assert.equal(costSum,6n*BigInt(M)+3n*E);
  assert.equal(correction,2n*D,'first M-one cancellation');
  assert.equal(correction,L*h+2n*B);
  // After Lzero=k-R, current rank 2*T-Delta,
  // current y=(2*D/4^R)*T. Both center arithmetic and costs exact.
  const zeroLength=k-BigInt(R);
  assert(zeroLength%2n===0n);
  const Delta=delta+costSum+3n*zeroLength;
  assert(Delta>12n && Delta<10n*k);
  const fourR=4n**BigInt(R),digits=[];
  let A=2n*D,err=0n,bitCost=0n,even=true;
  for(let j=0;j<R;j++){
    const d=(D/4n**BigInt(R-1-j))%4n;
    assert(d===0n||d===1n);digits.push(Number(d));
    const step=even?(d===0n?1n:3n):(d===0n?5n:9n);
    bitCost+=step;
    const offset=even?4n:12n;
    A=4n*A-2n*d*fourR;
    err=4n*err+d*(Delta+bitCost-offset);
    even=!even;
    assert(A>=0n&&err>=0n);
    assert(A>0n||err>0n);
    assert(3n*A<2n*fourR);
    // Exact sufficient cone inequality, after substituting
    // T > 100*k*4^(2R), avoiding construction of T.
    const gap=2n*fourR-3n*A;
    assert(100n*k*fourR*gap>36n*k+3n*err);
  }
  assert.equal(A,0n,'second Cantor-digit cancellation');
  assert(err>0n && err<4n*k*fourR);
  // The last q zeros have y=err*4^q. This source-independent
  // bound plus the rank floor 2*T-36*k ensures strictness.
  assert(3n*err<4n**BigInt(2*R+100*M));
  const N=m+3n*k-3n*S-104n*BigInt(M)+1n;
  assert(N%2n===0n && N>0n && N<4n*k);
  // Chronological halfstep pairing yields an actual signed q0 macro
  // word: every even-rank inverse predecessor has even height.
  const alphaNum=L*L,alphaDen=9n*4n**BigInt(2*M-1)-L*L;
  const frac=(v,w)=>Number(v*100000000n/w)/100000000;
  return {M,s,topExponent:top,nonzeroF,maxFExponent:maxFExp,
    lambda:L.toString(),beta:beta.toString(),residue:residue.toString(),
    F:F.toString(),m:m.toString(),h:h.toString(),k:k.toString(),
    R,N:N.toString(),NoverK:frac(N,k),asymptoticCoeff:3+frac(alphaNum,alphaDen),
    bitWord:digits.join(''),macroSteps:(N/2n).toString(),
    firstResetHeight:(2n*D).toString(),secondResetDigits:err.toString().length,
    coneBoundsChecked:true};
}
if(require.main===module){
  const args=process.argv.slice(2).map(Number);
  const cases=args.length===2?[args]:
    [[3,4],[3,6],[6,8],[9,10],[12,14],[15,16]];
  for(const [M,s] of cases)console.log(JSON.stringify(check(M,s)));
}
module.exports={check};
