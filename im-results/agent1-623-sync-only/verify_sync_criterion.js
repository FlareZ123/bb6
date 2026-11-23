#!/usr/bin/env node
"use strict";

// Independent finite regression check of the exact residue criterion.
// Exhausts every pair word of lengths 2,3,4 against direct full-rectangle simulation.

function starts(branch){
  const out=[];
  const amin=branch==="L"?-2:-4, amax=branch==="L"?2:1;
  for(let xp=0;xp<3;xp++) for(let yp=0;yp<3;yp++)
  for(let a=amin;a<=amax;a++) for(let b=-2;b<=2;b++)
    out.push([xp,yp,a,b]);
  return out;
}

function step(branch,s,z){
  const [xp,yp,a,b]=s, x=Math.floor(z/3), y=z%3;
  let tx,ty;
  if(branch==="L"){ tx=x-yp+a; ty=yp+b; }
  else { tx=-x-xp-yp+a; ty=xp+yp+b; }
  return [x,y,Math.floor(tx/3),Math.floor(ty/3)];
}

function directSync(branch,w){
  const images=new Set();
  for(const s0 of starts(branch)){
    let s=s0;
    for(const z of w) s=step(branch,s,z);
    images.add(s.join(","));
  }
  return images.size===1;
}

function residue(a,m){ const r=a%m; return r<0?r+m:r; }

function criterion(branch,w){
  const n=w.length, M=3**n;
  let X=0,Y=0,p=1;
  for(const z of w){ X+=Math.floor(z/3)*p; Y+=(z%3)*p; p*=3; }
  if(branch==="L"){
    const r1=residue(X-3*Y,M), r2=residue(3*Y,M);
    return 4<=r1 && r1<=M-3 && 2<=r2 && r2<=M-5;
  }
  const r1=residue(4*X+3*Y,M), r2=residue(3*(X+Y),M);
  return 2<=r1 && r1<=M-8 && 2<=r2 && r2<=M-7;
}

function decode(code,n){
  const w=Array(n);
  for(let i=n-1;i>=0;i--){ w[i]=code%9; code=Math.floor(code/9); }
  return w;
}

let checked=0;
for(let n=2;n<=4;n++){
  for(let code=0;code<9**n;code++){
    const w=decode(code,n);
    for(const branch of ["L","R"]){
      const a=directSync(branch,w), b=criterion(branch,w);
      if(a!==b) throw new Error("mismatch "+branch+" "+JSON.stringify(w));
      checked++;
    }
  }
}
console.log(JSON.stringify({checked, lengths:[2,3,4], mismatches:0}));
