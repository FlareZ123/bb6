#!/usr/bin/env node
'use strict';
const assert=require('node:assert/strict');

// Two-parameter exact strict inverse family. Fast-forward zero runs by the
// arithmetic identity for alternating rank costs, but test every one-step.
// No floating-point state, and no bound on intermediate center heights.
function check(t,s) {
  assert(Number.isSafeInteger(t) && t>=1 && t<=6);
  assert(Number.isSafeInteger(s) && s>=0 && s<=5);
  const M=3*t, powM=4n**BigInt(M);
  assert.equal((powM-1n)%9n,0n);
  const A=(powM-1n)/9n;
  const K=4n+2n*A*4n**BigInt(s), k=Number(K);
  assert(Number.isSafeInteger(k) && k>=2*M+s+7 && k<=4000000);
  const r=k-M-s, q=k-s-2*M, N=3*k-2*s-2*M;
  const T=4n**K,P=2n*T+4n;
  let p=P,y=2n,steps=0;
  function valid() {assert(p>=4n && y>0n && 3n*y<p);}
  function evenPhase() {if(p%2n===0n) assert.equal(y%2n,0n);}
  function zeroRun(n) {
    assert(Number.isSafeInteger(n) && n>=0);
    const even=p%2n===0n;
    const loss=BigInt(3*n+(n%2===1?(even?-2:2):0));
    p-=loss;
    y*=4n**BigInt(n);
    steps+=n;valid();evenPhase();
  }
  function one() {
    const even=p%2n===0n;
    p-=BigInt(even?3:9);
    y=4n*y-p-BigInt(even?4:12);
    steps++;valid();evenPhase();
  }
  zeroRun(k-1);
  assert.equal(y,T/2n);
  one();
  assert.equal(y,2n*((powM-1n)/3n)*4n**BigInt(s));
  zeroRun(r);
  assert.equal(y,2n*((powM-1n)/3n)*4n**BigInt(k-M));
  for(let j=0;j<M;j++) one();
  const H=y;
  assert(H>BigInt(k)*powM);
  zeroRun(q);
  assert.equal(steps,N);
  assert.equal(p%2n,0n);
  assert(12n*y>=p-1n && 4n*y<=p+1n,'reverse path not terminal');
  const loss=P-p;
  assert(loss<=9n*K);
  // Claim: terminal height/P lies in the forbidden inverse-band.
  assert(6n*y>T); // y > T/6
  assert(2n*y<T); // y < T/2
  return {t,s,M,k,r,q,N,rankLoss:loss.toString(),
    resetHeight:H.toString().slice(0,24),terminalHeightVsT:
      (Number(y*10000n/T)/10000).toFixed(4),terminal:true};
}
if(require.main===module){
  const t=process.argv[2]===undefined?1:Number(process.argv[2]);
  const s=process.argv[3]===undefined?0:Number(process.argv[3]);
  if(process.argv[2]===undefined) {
    for(const tt of [1,2,3])for(const ss of [0,1])
      console.log(JSON.stringify(check(tt,ss)));
  } else console.log(JSON.stringify(check(t,s)));
}
module.exports={check};
