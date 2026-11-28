#!/usr/bin/env node
'use strict';
const assert=require('node:assert/strict');

// Reproducible exact BigInt two-sided #429 signed halfstep/macro family.
// Symbolic mode handles arbitrary R without constructing 4^k.
// Direct mode materializes 4^k only when k<=200000 and independently
// replays all nonzero halfsteps and all source-macro exact divisions.

function parameters(R){
  assert(Number.isSafeInteger(R)&&R>=10&&R<=256);
  const F=R%3===1?69n:R%3===2?4161n:66645n;
  const D=4n**BigInt(R-1)+F;
  assert.equal(D%63n,7n);
  const h=2n*(D-14182n)/63n,k=h+228n;
  assert(h>0n&&h%2n===0n&&k%2n===0n);
  const q=k-2n*BigInt(R)-300n,N=3n*k-2n*BigInt(R)-74n;
  assert(q>0n&&N>h&&N%2n===0n);
  let rr=D;const bits=[];
  for(let j=0;j<R;j++){bits.unshift(Number(rr%4n));rr/=4n;}
  assert.equal(rr,0n);assert(bits.every(d=>d===0||d===1));
  const radius=h/2n;
  assert(k<4n**BigInt(R)&&k>=16n*BigInt(R));
  assert(k>4n*BigInt(R)+300n);
  // The first M=3 one block cancels T: H=28364+63h=2D.
  assert.equal(28364n+63n*h,2n*D);
  const lossFirst=679n+9n+(3n*(k-5n)-2n)+21n;
  assert.equal(lossFirst,3n*k+692n);
  const L=k-BigInt(R);
  const zeroLoss=L%2n===0n?3n*L:3n*L-2n;
  const Delta=3n*k+688n+zeroLoss;
  assert(Delta>0n&&Delta<10n*k);
  let C=0n,E=0n,pEven=L%2n===0n; // rank after 111 is even
  // parity at first digit is even iff the length L is even
  for(let j=0;j<R;j++){
    const bit=bits[j];
    const cost=BigInt(bit?(pEven?3:9):(pEven?1:5));
    C+=cost;
    const offset=BigInt(pEven?4:12);
    E=4n*E+BigInt(bit)*(Delta+C-offset);
    assert(E>=0n);
    pEven=!pEven;
  }
  assert(E>0n&&E<4n*k*(4n**BigInt(R)));
  // Exact extra-wide cone margin from T>=4^(4R+300) and k<4^R.
  assert(4n**BigInt(R+300)>100n*k);
  const result={R,F:F.toString(),D:D.toString(),h:h.toString(),
    k:k.toString(),N:N.toString(),macroPast:(N/2n).toString(),
    symmetricMacroRadius:radius.toString(),hOverK:
      Number(h*100000000n/k)/100000000,
    E:E.toString(),Rdigits:bits.join(''),symbolic:true};
  return {result,params:{R,D,h,k,q,N,bits,E}};
}

function direct(R){
  const {result,params}=parameters(R);
  const {D,h,k,q,N,bits,E}=params;
  assert(k<=200000n,'direct replay limit k<=200000; use symbolic mode');
  const K=Number(k),H=Number(h),Q=Number(q);
  const T=4n**k,P=2n*T+4n,Y=2n*4n**h;
  let p=P,y=Y,d=0;
  const chunks=[];
  const strict=()=>{assert(p>=4n&&y>0n&&3n*y<p);
    if(p%2n===0n)assert.equal(y%2n,0n);};
  const zr=n=>{
    assert(n>=0);
    p-=BigInt(3*n+(n%2?(p%2n===0n?-2:2):0));
    y*=4n**BigInt(n);d+=n;strict();
    chunks.push([0,n]);
  };
  const one=()=>{
    const even=p%2n===0n;
    p-=BigInt(even?3:9);
    y=4n*y-p-BigInt(even?4:12);d++;strict();
    chunks.push([1,1]);
  };
  strict();
  zr(227);assert.equal(y,T/2n);
  one();assert.equal(y,672n);
  zr(K-5);assert.equal(y,21n*T/32n);
  one();one();one();assert.equal(y,2n*D);
  zr(K-R);assert.equal(y,2n*D*4n**BigInt(K-R));
  for(const b of bits){if(b===0)zr(1);else one();}
  assert.equal(y,E);
  zr(Q);assert.equal(BigInt(d),N);

  // Independent *original radix-16 macro* replay, not just halfstep guard.
  const macro=[];
  const add=(digit,count)=>{
    if(count===0)return;
    const last=macro[macro.length-1];
    if(last&&last[0]===digit)last[1]+=count;
    else macro.push([digit,count]);
  };
  let pending=null;
  for(const [bit,len] of chunks.slice().reverse()){
    let n=len;
    if(pending!==null){add(pending+4*bit,1);n--;pending=null;}
    add(bit?5:0,Math.floor(n/2));n%=2;
    if(n===1)pending=bit;
  }
  assert.equal(pending,null);
  let mp=p/2n,my=y/2n,mc=0,nz=0;
  for(const [digit,count] of macro){
    assert(my>0n&&3n*my<mp);
    if(digit===0){
      const div=16n**BigInt(count);
      assert.equal(my%div,0n);
      my/=div;mp+=3n*BigInt(count);mc+=count;
    } else {
      for(let j=0;j<count;j++){
        assert([1,4,5].includes(digit));
        const off=BigInt(digit===1?6:digit===4?18:32);
        const cost=BigInt(digit===1?5:digit===4?4:6);
        const numerator=my+BigInt(digit)*mp+off;
        assert.equal(numerator%16n,0n);
        my=numerator/16n;mp+=cost;mc++;nz++;
      }
    }
    assert(my>0n&&3n*my<mp);
  }
  assert.equal(BigInt(mc)*2n,N);
  assert.equal(mp,T+2n);assert.equal(my,4n**h);

  // Exact full forward zero macro (h/2 steps) from the same center.
  const cnt=h/2n,den=16n**cnt;
  assert.equal((4n**h)%den,0n);
  assert.equal((4n**h)/den,1n);
  const endpoint=T+2n+3n*cnt;
  assert.equal(2n*endpoint,P+3n*h);
  result.direct=true;result.macroNonzeroDigits=nz;
  result.macroRuns=macro.length;
  result.forwardMacroEndpoint='(4^k+2+3*h/2,1)';
  return result;
}

if(require.main===module){
  const args=process.argv.slice(2);
  const Rs=args.length?args.map(Number):[10,11,12,13];
  for(const R of Rs)console.log(JSON.stringify(
    parameters(R).params.k<=200000n?direct(R):parameters(R).result));
}
module.exports={parameters,direct};
