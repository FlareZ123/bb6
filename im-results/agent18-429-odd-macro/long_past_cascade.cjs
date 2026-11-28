#!/usr/bin/env node
'use strict';
const assert=require('node:assert/strict');

// Unbounded second-resonance cascade in authentic signed #429 halfstep and
// radix-16 q0 macro arithmetic. The mathematical theorem is for *all*
// even s>=2; this executable samples bounded s because 4^k is enormous.
//
// All numbers used to represent ranks/heights/powers/corrections are BigInt.
// Zero runs fast-forward by an exact phase-dependent rank-cost identity.
// Every inverse one and every radix-16 nonzero digit is executed literally.
//
// No claim that any constructed synthetic state is blank-tape reachable.
function check(s) {
  assert(Number.isSafeInteger(s)&&s>=2&&s%2===0&&s<=10);
  const F=s%6===0?66645n:s%6===2?4161n:69n;
  const R=s+6,D=4n**BigInt(s+5)+F;
  const B=882n*4n**BigInt(s)+133n-63n*BigInt(s/2);
  const diff=D-B;
  assert(diff>0n && diff%63n===0n && D%63n===7n);
  const h=Number(2n*diff/63n),m=Number(3n+14n*4n**BigInt(s));
  const k=m+1+h,r=k-3-s,L=k-R,nFinal=k-2*R-20;
  assert([h,m,k,r,L,nFinal].every(x=>Number.isSafeInteger(x)&&x>0));
  assert(k%2===0 && m%2===1 && R<k/2);
  const T=4n**BigInt(k),P=2n*T+4n,Y=2n*4n**BigInt(h);
  let p=P,y=Y,steps=0,aChecks=0;
  const reverseChunks=[];
  const strict=()=>{
    assert(p>=4n&&y>0n&&3n*y<p,'strict cone failure at s='+s);
    if(p%2n===0n){aChecks++;assert.equal(y%2n,0n,'A phase parity');}
  };
  const record=(digit,count)=>{if(count>0)reverseChunks.push([digit,count]);};
  const zeros=n=>{
    const even=p%2n===0n;
    p-=BigInt(3*n+(n%2===1?(even?-2:2):0));
    y*=4n**BigInt(n);steps+=n;strict();
    record(0,n);
  };
  const one=()=>{
    const even=p%2n===0n;
    p-=BigInt(even?3:9);
    y=4n*y-p-BigInt(even?4:12);steps++;strict();
    record(1,1);
  };
  strict();
  zeros(m);assert.equal(y,T/2n);
  one();assert.equal(y,42n*4n**BigInt(s));
  zeros(r);assert.equal(y,21n*T/32n);
  for(let j=0;j<3;j++)one();
  assert.equal(y,2n*D,'second exact cancellation identity');
  zeros(L);assert.equal(y,2n*D*4n**BigInt(k-R));
  const bits=[];
  for(let i=R-1;i>=0;i--){
    const bit=Number((D/4n**BigInt(i))%4n);
    assert(bit===0||bit===1);
    bits.push(bit);
    if(bit===0)zeros(1);else one();
  }
  const afterBits=y;
  assert(afterBits>0n);
  zeros(nFinal);
  const N=m+3*k-3*s-31;
  assert.equal(steps,N);
  assert(N%2===0);
  const sourceStartP=p/2n,sourceStartY=y/2n;
  assert.equal(p%2n,0n);assert.equal(y%2n,0n);

  // Independently construct *chronological* source-macro word from paired
  // halfstep bits, without unrolling the huge zero blocks.
  const macros=[];const append=(d,n)=>{
    if(!n)return;
    const last=macros[macros.length-1];
    if(last&&last[0]===d)last[1]+=n;else macros.push([d,n]);
  };
  let pending=null;
  for(const [bit,len] of reverseChunks.slice().reverse()) {
    let n=len;
    if(pending!==null){append(pending+4*bit,1);n--;pending=null;}
    append(bit===0?0:5,Math.floor(n/2));n%=2;
    if(n===1)pending=bit;
  }
  assert.equal(pending,null);
  let mp=sourceStartP,my=sourceStartY,macroSteps=0,nonzeroDigits=0;
  const strictMacro=()=>assert(my>0n&&3n*my<mp);
  for(const [d,n] of macros){
    strictMacro();
    if(d===0){
      const denominator=16n**BigInt(n);
      assert.equal(my%denominator,0n);
      my/=denominator;mp+=3n*BigInt(n);macroSteps+=n;
    }else{
      for(let j=0;j<n;j++){
        assert([1,4,5].includes(d));
        const off=BigInt(d===1?6:d===4?18:32);
        const cost=BigInt(d===1?5:d===4?4:6);
        const numerator=my+BigInt(d)*mp+off;
        assert.equal(numerator%16n,0n);
        my=numerator/16n;mp+=cost;macroSteps++;nonzeroDigits++;
      }
    }
    strictMacro();
  }
  assert.equal(2*macroSteps,N);
  assert.equal(mp,T+2n);assert.equal(my,4n**BigInt(h));
  return {s,k,m,h,R,D:D.toString(),F:F.toString(),
    bits:bits.join(''),halfsteps:N,ratio:Number(N/k).toFixed(8),
    macroSteps,macroRuns:macros.length,nonzeroDigits,
    afterBitHeightDigits:afterBits.toString().length,aChecks};
}

if(require.main===module){
  const values=process.argv.slice(2).map(Number);
  const cases=values.length?values:[2,4,6,8];
  for(const s of cases)console.log(JSON.stringify(check(s)));
}
module.exports={check};
