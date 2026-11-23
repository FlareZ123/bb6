#!/usr/bin/env node
// Source-direct BigInt audit of JointSyncSquareGapNonclosure.md.
// Run: node im-results/agent1-623-sync-only/verify_joint_sync_square_gap_nonclosure.js
// The all-depth theorem is proved analytically in the adjacent note;
// finite ell=30..100 tests are an independent reproducibility check.
const pow3=n=>3n**BigInt(n),tau=n=>(pow3(n)-1n)/2n;
const mod=(a,m)=>(a%m+m)%m, floor=(a,m)=>a%m<0n?a/m-1n:a/m;
const ceil=(a,m)=>-floor(-a,m),requireTrue=(ok,msg)=>{if(!ok)throw Error(msg)};

// Direct transcription of upstream Cryptids evalA and drainB semantics.
function evalA(a,k,m){
 while(true){
  const j=k/3n,r=k%3n;
  if(r===2n)return [a+1n,j,m];
  if(r===0n)return a===0n?null:[a-1n,j,m+2n];
  if(a===0n)return [0n,j,m];
  a--;k=j;m+=2n*j+3n;
 }
}
function drainB(a,b,d){
 let calls=0n;
 while(b>0n){
  const v=evalA(a,b-1n,d+2n*b+3n);
  if(v===null)return null;
  [a,b,d]=v;
  if(++calls>10000n)throw Error('unexpected evaluator loop');
 }
 return {a,d,calls};
}
function highLevelNext(a,d){
 if(a===0n)return d%2n===1n?drainB(d+1n,2n,2n):{a:d,d:7n,calls:0n};
 if(d%2n===1n&&a>=d+5n)return drainB(a-d-5n,d+3n,5n);
 if(d%2n===0n&&a>=d+3n)return drainB(a-d-2n,d+2n,2n);
 if(a%2n===1n)return null;
 if(a===d+2n)return drainB(0n,a,2n);
 if(d%2n===1n)return drainB(d+4n-a,a-1n,3n);
 const z=evalA(d+1n-a,a,2n*a+5n);
 return z===null?null:drainB(...z);
}
function coneLE(a,d){
 if(d%2n!==0n||a<d+3n)return false;
 let k=0;
 while(tau(k)<d+2n)k++;
 return a-d-2n>=BigInt(k);
}
function window(a,d){
 const p=a>d?a-d:d-a,q=a>d?d:a,S=a+d;
 const gamma=a>d?(d%2n===0n?10n:18n):(d%2n===0n?4n:2n);
 let ell=0;while(tau(ell)<S+3n)ell++;
 const B=34n*BigInt(ell);
 const threshold=B+122n;
 let k=0,j=0;
 while(pow3(k)<=threshold)k++;
 while(pow3(j)<=threshold**3n)j++;
 const n=j-k-4,P=pow3(k+2),M=pow3(n),N=M/3n;
 requireTrue(n>=3,'too-short window');
 const X=2n*(p-3n*q)-gamma,Y=6n*q;
 const x=mod(floor(X,P),M),y=mod(floor(Y,P),M);
 const A=mod(x-3n*y,M),C=mod(4n*x+3n*y,M);
 const U=y%N,V=mod(x+y,N);
 return {ell,k,j,P,M,N,x,y,A,C,U,V,p,q,
   synchronized:A>=4n&&A<=M-3n&&C>=2n&&C<=M-8n&&
     U>=1n&&U<=N-2n&&V>=1n&&V<=N-3n};
}
for(let ell=30;ell<=100;ell++){
 const B=34n*BigInt(ell)+122n;
 let k=0,j=0;
 while(pow3(k)<=B)k++;
 while(pow3(j)<=B**3n)j++;
 const P=pow3(k+2),M=pow3(j-k-4),H=pow3(j-3);
 const t0=M%4n===1n?3n:1n;
 const q0=pow3(k+1)*(1n+M*t0)/2n;
 const lo=floor(tau(ell-1)+9n*BigInt(ell)-37n-5n*P,14n)+1n;
 const hi=floor(tau(ell)-20n*BigInt(ell)-43n-5n*P,15n);
 const r=q0<lo?ceil(lo-q0,2n*H):0n,q=q0+2n*H*r;
 requireTrue(q>0n&&q<=hi&&q%2n===0n,'q interval/parity at ell '+ell);

 // Extract signed digit drop and call count independently from the original
 // evaluator at baseline first counter; then form the source state.
 const baseline=drainB(3n*q-2n,q+2n,2n);
 requireTrue(baseline!==null,'unexpected baseline halt at ell '+ell);
 const D=3n*q-2n-baseline.a,R=baseline.calls;
 requireTrue(D>=-BigInt(ell)&&D<=BigInt(ell)&&R<=BigInt(ell),
    'source depth bounds at ell '+ell);
 const c=9n*q+9n*D+8n*R+34n+5n*P;
 const a=4n*q+c,d=q;
 const next=highLevelNext(a,d);
 requireTrue(next!==null,'unexpected source halt at ell '+ell);
 requireTrue(next.a===baseline.a+c&&next.d===baseline.d,
    'source affine shift at ell '+ell);
 requireTrue(coneLE(a,d)&&coneLE(next.a,next.d),
    'both LE cone budgets at ell '+ell);

 const src=window(a,d),dst=window(next.a,next.d);
 requireTrue(src.ell===ell&&dst.ell===ell&&src.k===dst.k&&src.j===dst.j,
    'identical mass-indexed cuts at ell '+ell);
 requireTrue((src.x===12n||src.x===13n)&&src.y===1n&&src.synchronized,
    'source joint synchronization at ell '+ell);
 requireTrue(dst.x===9n&&(dst.y===2n||dst.y===3n)&&!dst.synchronized,
    'target left synchronization failure at ell '+ell);
 requireTrue(dst.A===0n||dst.A===3n,'target left forbidden residue at ell '+ell);

 const g=src.p-3n*src.q,gp=dst.p-3n*dst.q;
 const h=g-5n,hp=gp-5n;
 requireTrue(g>8n*q&&h*h>5n*q,'source strong square gap at ell '+ell);
 requireTrue(gp===5n*P&&hp*hp<dst.q,
    'target exact gap and strict square gap failure at ell '+ell);

 if([30,40,50,70,100].includes(ell))
  console.log('ell='+ell,
   'D('+a+','+d+') -> D('+next.a+','+next.d+')',
   'sourceWindow=('+src.x+','+src.y+')',
   'targetWindow=('+dst.x+','+dst.y+')',
   'targetGap='+gp,'targetQ='+dst.q,'drainCalls='+R);
}
console.log('PASS: 71 source-direct cases ell=30..100: equal cuts, cone-to-cone, source sync+square-gap, target failure of BOTH');
