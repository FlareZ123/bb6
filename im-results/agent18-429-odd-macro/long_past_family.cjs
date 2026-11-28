#!/usr/bin/env node
'use strict';
const assert = require('node:assert/strict');

// Infinite exact one-sided signed half-step family at
// P=2*4^k+4, Y=2, k=14*4^s+4.
// The bits below are in reverse chronological order.
function check(s) {
  assert(Number.isSafeInteger(s) && s >= 0 && s <= 7);
  const k = 14 * 4 ** s + 4;
  assert(Number.isSafeInteger(k));
  const T = 4n ** BigInt(k), P = 2n*T+4n;
  const m=k-1,r=k-s-3,q=k-s-6;
  let p=P,y=2n,depth=0,parityTests=0;
  const stages=[];
  const word=[['0',m],['1',1],['0',r],['1',3],['0',q]];
  for (const [digit,count] of word) {
    for (let i=0;i<count;i++) {
      const wasEven = p%2n===0n;
      if (wasEven) {assert.equal(y%2n,0n);parityTests++;}
      const cost=BigInt(digit==='0'?(wasEven?1:5):(wasEven?3:9));
      const nextP=p-cost;
      const nextY=4n*y-(digit==='1'?nextP+BigInt(wasEven?4:12):0n);
      assert(nextP>=4n && nextY>0n && 3n*nextY<nextP,
        'failure at s='+s+', depth='+depth+', bit='+digit);
      p=nextP; y=nextY; depth++;
    }
    stages.push({digit,count,rankLoss:P-p,height:y});
  }
  assert.equal(p%2n,0n);assert.equal(y%2n,0n);parityTests++;
  assert.equal(depth,3*k-2*s-6);
  const expectedZeroLoss=3*k-5;
  assert.equal(stages[0].rankLoss,BigInt(expectedZeroLoss));
  assert.equal(stages[0].height,T/2n);
  assert.equal(stages[1].rankLoss,BigInt(3*k+4));
  assert.equal(stages[1].height,42n*4n**BigInt(s));
  assert.equal(stages[2].height,21n*T/32n);
  const expectedAfterThree=(r%2===0?63*(k+r)-5:63*(k+r)-49);
  assert.equal(stages[3].height,BigInt(expectedAfterThree));
  assert.equal(stages[4].height,BigInt(expectedAfterThree)*4n**BigInt(q));
  // Independently replay the same history in the exact radix-16 q0 macro.
  // Macro digit 0/1/4/5 corresponds to chronological halfstep pairs
  // 00/10/01/11 respectively.
  const macro=[];
  const appendMacro=(d,n)=>{for(let j=0;j<n;j++) macro.push(d);};
  if(s%2===0) {
    appendMacro(0,q/2); macro.push(5,1);
    appendMacro(0,(r-1)/2); macro.push(1);
    appendMacro(0,(k-2)/2);
  } else {
    appendMacro(0,(q-1)/2); macro.push(4,5);
    appendMacro(0,r/2); macro.push(1);
    appendMacro(0,(k-2)/2);
  }
  assert.equal(2*macro.length,depth);
  let mp=p/2n,my=y/2n;
  for(const d of macro) {
    assert(my>0n && 3n*my<mp);
    const length=BigInt(d===0?3:d===1?5:d===4?4:6);
    const offset=BigInt(d===0?0:d===1?6:d===4?18:32);
    const numerator=my+BigInt(d)*mp+offset;
    assert.equal(numerator%16n,0n);
    mp+=length;my=numerator/16n;
  }
  assert.equal(mp,T+2n);assert.equal(my,1n);
  return {s,k,reverseSteps:depth,rankLoss:(P-p).toString(),
    evenPhaseLatticeChecks:parityTests,
    thirdResetHeight:expectedAfterThree,
    terminalHeightDigits:y.toString().length};
}

if(require.main===module) {
  const start=process.argv[2]===undefined?0:Number(process.argv[2]);
  const end=process.argv[3]===undefined?4:Number(process.argv[3]);
  for (let s=start;s<=end;s++) console.log(JSON.stringify(check(s)));
}
module.exports={check};
