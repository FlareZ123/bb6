# Higher-power root-prefix relaxation: no gain beyond mod 128

Agent 45, 2026-11-24.

## Question

Does the existing reverse-parent root-prefix relaxation become stronger for the two unresolved restart classes by lifting its modulus from 128 to 256, 512, or 1024?

## Result

No. Re-running the same all-positive-cost relaxation at all three moduli preserves exactly the same root-membership split for both restart families and every (h\in\{0,\ldots,7\}):

- (h\equiv0,3\pmod4): the root ((2,0)) is **not** in the closure.
- (h\equiv1,2\pmod4): the root **is** in the closure.

Every tested start closure has the following size, independent of family and (h):

| Modulus | Closure size |
|---:|---:|
| 256 | 4,928 |
| 512 | 17,784 |
| 1024 | 63,424 |

Thus a straightforward lift of the existing mod-128 graph cannot close the (h\equiv1,2\pmod4) classes. This is a negative result about this relaxation, not about actual blank reachability. The relaxed graph permits arbitrary positive inverse costs and is only a necessary-condition filter.

## Reproduction

The following standalone Node.js script reproduces the calculation. The two start-family formulae are the same ones used by the existing `root_prefix_mod128.js`; the only change is the modulus and the full eight residue classes of (h\bmod8).

```javascript
'use strict';
const mod=(x,m)=>((x%m)+m)%m;
const powMod=(a,e,m)=>{
  let r=1n%m,b=a%m;
  while(e>0n){if(e&1n)r=r*b%m;b=b*b%m;e>>=1n;}
  return r;
};
const families=[
  {name:'I',n0:5362n,delta:595056n,a:17n,b:1058n,c:636n},
  {name:'II',n0:9538n,delta:703248n,a:87n,b:1198n,c:712n},
];
function start(f,h,M){
  const n=f.n0+f.delta*BigInt(h), modulus=f.b*49n*BigInt(M);
  const P=powMod(2n,n,modulus);
  const un=mod(f.a*P-f.c,modulus);
  if(un%f.b) throw Error('u division');
  const u=un/f.b;
  const dn=mod(18n*P-196n*u+14n*n+48n,49n*BigInt(M));
  if(dn%49n) throw Error('D division');
  return {
    D:Number(dn/49n),
    m:Number(mod(14n*u-2n*n-3n,BigInt(M))),
    N0:Number(mod(14n*P-2n*n-7n,BigInt(M)))
  };
}
function closure(s,M){
  const log=Math.log2(M), mask=M-1;
  if(!Number.isInteger(log)) throw Error('power of two only');
  const costs=[],pows=[];
  for(let k=1;k<log;k++){costs.push(k);pows.push(1<<k);}
  // For k >= log2(M), 2^k = 0 mod M. A block of M
  // consecutive costs realizes every possible m' residue.
  for(let k=log;k<log+M;k++){costs.push(k);pows.push(0);}
  const seen=new Uint8Array(M*M),queue=new Uint32Array(M*M);
  let head=0,tail=0;
  const id=s.D*M+s.m;
  seen[id]=1;queue[tail++]=id;
  while(head<tail){
    const v=queue[head++],D=Math.floor(v/M),m=v%M;
    for(let i=0;i<costs.length;i++){
      const mp=(m-costs[i])&mask;
      const Dp=(pows[i]*D-s.N0+2*mp-1)&mask;
      const w=Dp*M+mp;
      if(!seen[w]){seen[w]=1;queue[tail++]=w;}
    }
  }
  return {states:tail,root:!!seen[2*M]};
}
for(const M of [256,512,1024]){
  console.log('MOD',M);
  for(const f of families){
    for(let h=0;h<8;h++){
      const s=start(f,h,M),r=closure(s,M);
      console.log(f.name,'h',h,'states',r.states,'root',r.root);
    }
  }
}
```

## Research consequence

Do not spend further effort merely increasing the modulus in this same relaxed graph. Closing (h\equiv1,2\pmod4) requires information discarded by the all-positive-cost relaxation, or a different forward/blank-specific invariant.
