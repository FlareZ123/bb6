#!/usr/bin/env node
// Exact all-index fan-in witnesses for #746 canonical inverse rays.
// Usage: node every_gate_ray_fanin.mjs <n> <m>
// No floating-point computations, dependencies, or enumeration of Turing steps.
const [nArg,mArg] = process.argv.slice(2);
if (!/^\d+$/.test(nArg||'') || !/^\d+$/.test(mArg||'')) {
  throw Error('usage: node every_gate_ray_fanin.mjs <n> <m>');
}
const n = BigInt(nArg), m = Number(mArg);
if (!Number.isSafeInteger(m) || m < 1 || n % 6n !== 4n && n % 6n !== 5n) {
  throw Error('require m >= 1 and n modulo 6 in {4,5}');
}
const T = 3*m + 1, mod = 3n ** BigInt(T);
if (n < 100n * mod) throw Error('theorem range: n >= 100*3^(3m+1)');
function powmod(a,e,q) {
  let out=1n; a%=q;
  while(e>0n) { if(e&1n) out=out*a%q; a=a*a%q; e>>=1n; }
  return out;
}
const c=2n*n+3n;
const Ares=(8n*powmod(2n,n,mod)+2n*n+3n)%mod;
function norm(x,q) { return (x%q+q)%q; }
let r=0n;
if (norm(Ares-2n*c,3n)!==0n) throw Error('invalid initial gate residue');
for(let e=1;e<T;e++) {
  const Q=3n**BigInt(e+1), step=3n**BigInt(e-1);
  let options=[];
  for(let d=0n;d<3n;d++) {
    let candidate=r+d*step;
    if(norm(Ares-2n*c*powmod(4n,candidate,Q),Q)===0n) options.push(candidate);
  }
  if(options.length!==1) throw Error('Hensel uniqueness failure at precision '+(e+1));
  r=options[0];
}
const j=2n*r, p=1n<<n;
const a=BigInt(c.toString(2).length-1), J=n-a;
if(j+8n>J || j>=2n*3n**BigInt(T-1)) throw Error('ray bound failure');
const u=4n*p+n-1n-c*(1n<<j);
const X=2n*u+5n;
if(X%mod!==0n || !(7n*p<X && X<9n*p)) throw Error('numerator bound failure');
const even=u-(c*(1n<<j)); // u_(j+1)
const ke=n-1n, pe=1n<<ke;
if(!(6n*pe-1n<=u && u<=8n*pe-3n)
   || 2n*u!==8n*pe+even+ke || even<=3n*p)
  throw Error('canonical even parent invalid');
let odd=[];
for(let b=0;b<m;b++) {
  let block=[];
  for(let t=3*b;t<=3*b+2;t++) {
    const tb=BigInt(t), den=3n**(tb+1n);
    if(X%den!==0n) continue;
    const d=X/den, q=(1n<<tb)*d;
    const k=BigInt(q.toString(2).length-3);
    if(k<1n) continue;
    const pk=1n<<k;
    if(!(6n*pk+1n<=q && q<=8n*pk-1n)) continue;
    const h=2n*q-8n*pk-k-5n;
    if(d%2n!==1n || h<0n || 2n*q!==8n*pk+h+k+5n
       || 3n**(tb+1n)*d!==X || h>=2n*p)
      throw Error('invalid odd-source witness in block '+b);
    block.push({t,k:Number(k),h});
  }
  if(!block.length) throw Error('no odd source parent in block '+b);
  odd.push(...block);
}
const v=T-1, dAll=X/mod;
if(dAll<=1n || dAll%2n!==1n) throw Error('terminal quotient lower bound failed');
const log2=z=>BigInt(z.toString(2).length-1);
const expectedC=2n*BigInt(v)+log2(dAll)-log2(3n**BigInt(v)*dAll);
let observedC=0n;
for(let t=0;t<v;t++) {
  const tb=BigInt(t), d=X/(3n**(tb+1n)), q=(1n<<tb)*d;
  const k=BigInt(q.toString(2).length-3);
  if(k<1n) continue;
  const pk=1n<<k;
  if(d%2n===1n && 6n*pk+1n<=q && q<=8n*pk-1n) observedC++;
}
if(observedC!==expectedC) throw Error('exact source odd-count formula failed');
const lowerC=2n*BigInt(v)-BigInt((3n**BigInt(v)).toString(2).length);
const parents=[even,...odd.map(x=>x.h)];
if(new Set(parents.map(x=>x.toString())).size!==parents.length)
  throw Error('distinctness failure');
const report={n:n.toString(),m,T,j:j.toString(),J:J.toString(),
  verifiedOddValuations:odd.map(x=>x.t),
  totalDistinctParents:parents.length,
  atLeast:m+1,exactNonterminalOddCount:expectedC.toString(),directCount:observedC.toString(),minimumOddCount:lowerC.toString(),sourceBandChecked:true,evenBandChecked:true};
console.log(JSON.stringify(report,null,2));
