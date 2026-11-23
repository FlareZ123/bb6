#!/usr/bin/env node
// BigInt original-source arithmetic: one small counterexample + ell=20..50 family.
// The all-ell theorem is in InfiniteConeSyncNonclosure.md; these finite checks
// are its reproducibility audit, not a substitute for the universal proof.
const pow3=n=>3n**BigInt(n),tau=n=>(pow3(n)-1n)/2n;
const mod=(a,m)=>(a%m+m)%m;
const floor=(a,m)=>a%m<0n?a/m-1n:a/m;
const check=(v,msg)=>{if(!v)throw Error(msg)};
function evalA(a,k,m){while(true){
  const j=k/3n,r=k%3n;
  if(r===2n)return [a+1n,j,m];
  if(r===0n)return a===0n?null:[a-1n,j,m+2n];
  if(a===0n)return [0n,j,m];
  a--;k=j;m+=2n*j+3n;
}}
function drainB(a,b,d){let calls=0;while(b>0n){
  const v=evalA(a,b-1n,d+2n*b+3n);
  if(v===null)return null;
  [a,b,d]=v;
  if(++calls>10000)throw Error('drain did not terminate');
}return {a,d,calls};}
function highLevelNext(a,d){
  if(a===0n)return d%2n===1n?drainB(d+1n,2n,2n):{a:d,d:7n,calls:0};
  if(d%2n===1n&&a>=d+5n)return drainB(a-d-5n,d+3n,5n);
  if(d%2n===0n&&a>=d+3n)return drainB(a-d-2n,d+2n,2n);
  if(a%2n===1n)return null;
  if(a===d+2n)return drainB(0n,a,2n);
  if(d%2n===1n)return drainB(d+4n-a,a-1n,3n);
  const v=evalA(d+1n-a,a,2n*a+5n);
  return v===null?null:drainB(...v);
}
function window(a,d){
  const p=a>d?a-d:d-a,q=a>d?d:a,S=a+d;
  const gamma=a>d?(d%2n===0n?10n:18n):(d%2n===0n?4n:2n);
  let ell=0;while(tau(ell)<S+3n)ell++;
  const B=34n*BigInt(ell)+122n;let k=0,j=0;
  while(pow3(k)<=B)k++;
  while(pow3(j)<=B**3n)j++;
  const n=j-k-4,P=pow3(k+2),M=pow3(n),N=M/3n;
  check(n>=3,'window too short');
  const X=2n*(p-3n*q)-gamma,Y=6n*q;
  const x=mod(floor(X,P),M),y=mod(floor(Y,P),M);
  const A=mod(x-3n*y,M),C=mod(4n*x+3n*y,M),U=y%N,V=mod(x+y,N);
  return {ell,k,j,n,P,M,x,y,V,
    good:A>=4n&&A<=M-3n&&C>=2n&&C<=M-8n&&
         U>=1n&&U<=N-2n&&V>=1n&&V<=N-3n};
}
// For a large input p=a-d, avoid ever computing the astronomical 3^p:
// if p-2>=d+2, then tau(p-2)>=p-2>=d+2 immediately.
function coneLE(a,d){
  if(d%2n!==0n||a<d+3n)return false;
  const exponent=a-d-2n;
  if(exponent>=d+2n)return true;
  return d+2n<=tau(Number(exponent));
}
function coneRE(a,d){
  if(a===0n||a%2n!==0n||d%2n!==0n||a>=d)return false;
  const exponent=d+1n-a;
  if(exponent>=a+1n)return true;
  return a<tau(Number(exponent));
}
{
  const out=highLevelNext(4388n,1094n);
  check(out!==null&&out.a===3284n&&out.d===3310n,'small exact transition');
  const x=window(4388n,1094n),y=window(out.a,out.d);
  check(coneLE(4388n,1094n)&&coneRE(out.a,out.d),'small cone');
  check(x.good&&!y.good&&x.x===0n&&x.y===1n&&y.V===0n,'small sync');
  console.log('small source-faithful witness PASS');
}
for(let ell=20;ell<=50;ell++){
  const c=20n*BigInt(ell),B=34n*BigInt(ell)+122n;
  let k=0,j=0;while(pow3(k)<=B)k++;while(pow3(j)<=B**3n)j++;
  const M=pow3(j-k-4),t0=M%4n===1n?3n:1n;
  const G=2n*pow3(j-3),q0=pow3(k+1)*(1n+M*t0)/2n;
  const low=floor(tau(ell-1)-c-3n,5n)+1n;
  const high=floor(tau(ell)-c-3n,5n);
  const r=q0<low?(low-q0+G-1n)/G:0n,q=q0+r*G;
  check(q<=high&&q%2n===0n,'progression ell='+ell);
  const a=4n*q+c,d=q,out=highLevelNext(a,d);
  check(coneLE(a,d)&&out!==null&&coneLE(out.a,out.d),'cone ell='+ell);
  const x=window(a,d),y=window(out.a,out.d);
  check(x.ell===ell&&x.x===0n&&x.y===1n&&x.good,'input ell='+ell);
  check(!y.good&&(y.V===0n||y.V===y.M/3n-1n),'output ell='+ell);
  if(ell===20||ell===50)
    console.log('ell',ell,'PASS D('+a+','+d+') -> D('+out.a+','+out.d+')');
}
console.log('PASS: 31 depth instances and the small two-call witness');
