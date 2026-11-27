#!/usr/bin/env node
'use strict';
// Exact modular regressions for the Space Needle 35-adic four-valuation tower.
// Arithmetic evidence only: not a Lean or original-Cryptids theorem.
const assert = require('node:assert/strict');
const mod = (a, n) => ((a % n) + n) % n;
function power(a, e, n) {
  let b=mod(a,n), out=1n;
  while(e>0n){ if(e&1n)out=(out*b)%n; b=b*b%n;e>>=1n; }
  return out;
}
function inverse(a,n){
  let [r,s]=[n,mod(a,n)], [u,v]=[0n,1n];
  while(s){let q=r/s; [r,s]=[s,r-q*s];[u,v]=[v,u-q*v];}
  assert.equal(r,1n); return mod(u,n);
}
function modulus(k){ return 35n**BigInt(k); }
function cancellationMod(r,k){
  assert(r>=1n && k>=1);
  const M=modulus(k), ord2=12n*modulus(k-1);
  const a=((power(9n,r,2n*ord2)+5n)/2n)%ord2;
  const A=power(2n,a,M);
  assert.equal(A%35n,23n);
  const Pnum=mod(power(A,2n*r,M)-power(9n,r,M),M);
  return mod(A*Pnum*inverse(2n*(A+3n),M),M);
}
function target(k){
  let C=0n;
  for(let i=0;i<k;i++) C=32n*C-80n*modulus(i);
  return mod(-C*inverse(power(32n,BigInt(k),modulus(k)),modulus(k)),modulus(k));
}
const slope=[28n,15n,18n,0n,8n,25n];
for(let k=1;k<=5;k++){
  const M=modulus(k+1),P=6n*modulus(k-1);
  for(let r=1n;r<=36n;r++){
    const left=cancellationMod(r+P,k+1),right=cancellationMod(r,k+1);
    assert.equal(mod(left-right,M),slope[Number(r%6n)]*modulus(k)%M);
  }
}
let classes=[];
for(let r=1n;r<=210n;r++)if(cancellationMod(r,2)===target(2))classes.push(Number(r));
assert.deepEqual(classes,[88]);
console.log('Depth two: r == 88 (mod 210), 210-residue audit:',classes);
let r=4n;
assert.equal(cancellationMod(r,1),target(1));
console.log('k=1: r == 4 (mod 6), selected branch');
for(let k=1;k<=9;k++){
  const M=modulus(k+1),base=modulus(k), period=6n*modulus(k-1);
  assert.equal(mod(cancellationMod(r,k+1)-target(k),base),0n);
  const v=mod(target(k+1)-cancellationMod(r,k+1),M);
  assert.equal(v%base,0n);
  const j=mod((v/base)*inverse(8n,35n),35n);
  const next=r+j*period;
  assert.equal(cancellationMod(next,k+1),target(k+1));
  assert.equal(next%6n,4n);
  console.log('k='+String(k+1)+': r='+next+' (mod '+(period*35n)+'), lift digit='+j+', B residue='+target(k+1));
  r=next;
}
console.log('PASS: modular regression and ten 35-adic tower representatives');
