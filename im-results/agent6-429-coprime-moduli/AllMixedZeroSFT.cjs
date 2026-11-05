'use strict';

/** Independent executable finite checks for Agent6's nested-exponential period proof.
 * Exact BigInt arithmetic; modulus survey and witness construction are tests, not proof.
 * The general all-modulus theorem is proved mathematically in AllMixedModuliZeroSector.md.
 */

const assert = require('node:assert/strict');

/** @param {number} a @param {number} b */
function gcd(a, b) { while (b) [a,b]=[b,a%b]; return a; }
/** @param {number} a @param {number} b */
function lcm(a,b) { return a/gcd(a,b)*b; }
/** @param {number} n */
function phi(n) {
  let r=n, v=n;
  for (let p=2; p*p<=v; p++) {
    if(v%p) continue;
    while(v%p===0) v/=p;
    r-=r/p;
  }
  if(v>1) r-=r/v;
  return r;
}
/** @param {bigint} a @param {bigint} b */
function mod(a,b) { const r=a%b; return r<0n?r+b:r; }
/** @param {bigint} base @param {bigint} exp @param {bigint} m */
function powmod(base, exp, m) {
  let a=mod(base,m),e=exp,r=1n%m;
  while(e>0n) { if(e&1n) r=r*a%m; a=a*a%m; e>>=1n; }
  return r;
}
/** @param {number} v */
function v2(v){let i=0;while(v%2===0&&v>0){v/=2;i++;}return i;}
/** @param {number} c @param {number} m */
function directH(c,m) {
  const n=BigInt(c), powc=1n<<n, exponent=4n*powc+n-10n, M=BigInt(m);
  return Number(mod(4n*powmod(2n,exponent,M)-8n*powmod(2n,n,M)+13n-n,M));
}
/** @param {number} m */
function periodData(m) {
  const first=phi(m), second=phi(first), p=lcm(first,second), g=gcd(m,p);
  return {first,second,p,g,cutoff:Math.max(2,v2(m),v2(first))};
}
const residueCache=new Map();
/** Evaluate H(c) mod m using its independently checked eventual affine period. @param {number} c @param {number} m */
function hmod(c,m) {
  const {p,cutoff}=periodData(m);
  if(c<cutoff) return directH(c,m);
  const representative=cutoff+(c-cutoff)%p, shifts=(c-representative)/p;
  const key=m+':'+representative;
  if(!residueCache.has(key)) residueCache.set(key,directH(representative,m));
  return Number(mod(BigInt(residueCache.get(key))-BigInt(shifts)*BigInt(p),BigInt(m)));
}
/** @param {number} a @param {number} m */
function inverse(a,m){
  if(m===1)return 0;
  for(let i=1;i<m;i++)if(a*i%m===1)return i;
  throw new Error('missing modular inverse '+a+' / '+m);
}
/** Constructively realize every H0 residue, inducting on the proper gcd. @param {number} m @param {number} r @param {number} cutoff */
function witness(m,r,cutoff=2){
  if(m===1)return Math.max(2,cutoff);
  const {p,g,cutoff:C}=periodData(m);
  assert(g<m);
  const c=witness(g,r%g,Math.max(cutoff,C)), h=hmod(c,m);
  assert.equal(((h-r)%g+g)%g,0);
  const reduced=m/g;
  const v=Number(mod(BigInt((h-r)/g)*BigInt(inverse(p/g,reduced)),BigInt(reduced)));
  const answer=c+p*v;
  assert(Number.isSafeInteger(answer));
  assert.equal(hmod(answer,m),r%m);
  return answer;
}

let cases=0, largestIndex=0;
for(let m=1;m<=240;m++) {
  const {p,g,cutoff}=periodData(m);
  if(m>1)assert(g<m);
  for(let c=cutoff;c<=cutoff+Math.min(p,25);c++) {
    assert.equal((directH(c+p,m)-directH(c,m)+p)%m,0);
    cases++;
  }
  for(let r=0;r<m;r++) {
    const c=witness(m,r);
    largestIndex=Math.max(largestIndex,c);
    assert.equal(hmod(c,m),r);
    cases++;
  }
  if(m<=150&&m%3===0) {
    for(let r=0;r<m;r+=3) {
      const target=Number(mod(BigInt(r/3),BigInt(m)));
      const c=witness(m,target);
      assert.equal(3*hmod(c,m)%m,r);
      cases++;
    }
  }
  if(m%40===0) console.log('checked m<=',m,'period',p,'gcd',g,'largest constructed index',largestIndex);
}
console.log('PASS: exact BigInt periodicity, recursive all-residue witnesses and residue-zero sector;',cases,'checks, m<=240; max c=',largestIndex);
