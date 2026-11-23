#!/usr/bin/env node
// Exact finite independent audit of SharpTwoDigitCompletion.md.
// Node.js: node count_two_digit_completions.js
// The uniform all-n >=3 theorem is proved algebraically in the markdown.
const mod=(x,m)=>(x%m+m)%m;
function synced(U,V,M){
  const A=mod(V-4*U,M),C=mod(4*V-U,M),N=M/3;
  return A>=4&&A<=M-3&&C>=2&&C<=M-8&&
    U%N>=1&&U%N<=N-2&&V%N>=1&&V%N<=N-3;
}
for(let n=3;n<=5;n++){
  const M=3**n,M2=9*M;
  let minimum=81,maximum=0,badPrefixes=0,witnesses=[],hist=new Map();
  for(let U=0;U<M;U++)for(let V=0;V<M;V++){
    let count=0;
    for(let u=0;u<9;u++)for(let v=0;v<9;v++){
      if(synced(U+M*u,V+M*v,M2))count++;
    }
    minimum=Math.min(minimum,count);maximum=Math.max(maximum,count);
    hist.set(count,(hist.get(count)||0)+1);
    if(count===24&&witnesses.length<8)witnesses.push([U,V]);
    if(!synced(U,V,M))badPrefixes++;
    if(count<24)throw Error('violates minimum at n='+n+',U='+U+',V='+V);
  }
  if(minimum!==24)throw Error('sharp bound not attained at n='+n);
  console.log(JSON.stringify({n,M,prefixes:M*M,badPrefixes,minimum,maximum,
    examplesAtMinimum:witnesses,histogram:Object.fromEntries([...hist].sort((a,b)=>a[0]-b[0]))}));
}
console.log('PASS: sharp lower bound 24 for n=3,4,5; proof handles all n>=3');
