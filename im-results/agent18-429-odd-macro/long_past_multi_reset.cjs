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
  // Independently execute the exact aligned radix-16 q0 macro word.
  // Coalescing chronological halfsteps is determined by the parity of
  // s and M; this is independent from the reverse one-step simulation.
  const blocks=[];
  const add=(digit,count)=>{if(count>0)blocks.push([digit,count]);};
  if(s%2===0){
    add(0,q/2);
    if(M%2===0) { add(5,M/2);add(0,r/2);add(1,1); }
    else { add(5,(M-1)/2);add(1,1);add(0,(r-1)/2);add(1,1); }
  } else {
    add(0,(q-1)/2);add(4,1);
    if(M%2===0) { add(5,(M-2)/2);add(1,1);add(0,(r-1)/2);add(1,1); }
    else { add(5,(M-1)/2);add(0,r/2);add(1,1); }
  }
  add(0,(k-2)/2);
  let mp=p/2n,my=y/2n,macroCount=0;
  for(const [digit,count] of blocks) {
    assert(my>0n && 3n*my<mp);
    if(digit===0) {
      const pow=16n**BigInt(count);
      assert.equal(my%pow,0n,'zero macro exact division');
      my/=pow;
      mp+=3n*BigInt(count);
      macroCount+=count;
    } else {
      for(let i=0;i<count;i++) {
        const cost=BigInt(digit===1?5:digit===4?4:6);
        const offset=BigInt(digit===1?6:digit===4?18:32);
        const numerator=my+BigInt(digit)*mp+offset;
        assert.equal(numerator%16n,0n,'nonzero macro exact division');
        my=numerator/16n;mp+=cost;macroCount++;
      }
    }
    assert(my>0n && 3n*my<mp);
  }
  assert.equal(macroCount*2,N);
  assert.equal(mp,T+2n);assert.equal(my,1n);
  // At the macro endpoint, no digit is integrable: none of 0,1,4,5
  // gives a numerator divisible by 16, since T is divisible by 16.
  for(const [digit,offset] of [[0,0],[1,6],[4,18],[5,32]]) {
    assert.notEqual((1n+BigInt(digit)*(T+2n)+BigInt(offset))%16n,0n);
  }
  return {t,s,M,k,r,q,N,rankLoss:loss.toString(),
    resetHeight:H.toString().slice(0,24),terminalHeightVsT:
      (Number(y*10000n/T)/10000).toFixed(4),terminal:true,macroVerified:true,macroBlocks:blocks.length};
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
