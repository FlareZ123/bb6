#!/usr/bin/env node
// Exact source-direct BigInt audit for RobustConeSyncNonclosure.md.
// Node.js: node im-results/agent1-623-sync-only/verify_robust_cone_sync_nonclosure.js
// Audits ell=30..100. Universal quantifier follows from the paper proof.
const pow3=n=>3n**BigInt(n), tau=n=>(pow3(n)-1n)/2n;
const mod=(a,m)=>(a%m+m)%m, floor=(a,m)=>a%m<0n?a/m-1n:a/m;
const ceil=(a,m)=>-floor(-a,m);
const check=(x,msg)=>{if(!x)throw Error(msg)};

// Literal source evalA and drainB, not the (p,q) canonical recurrence.
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
 let calls=0;
 while(b>0n){
  const t=evalA(a,b-1n,d+2n*b+3n);
  if(t===null)return null;
  [a,b,d]=t;calls++;
  if(calls>10000)throw Error('unexpectedly long drain');
 }
 return {a,d,calls};
}
function highLevelNext(a,d){
 if(a===0n)return d%2n===1n?drainB(d+1n,2n,2n):{a:d,d:7n,calls:0};
 if(d%2n===1n&&a>=d+5n)return drainB(a-d-5n,d+3n,5n);
 if(d%2n===0n&&a>=d+3n)return drainB(a-d-2n,d+2n,2n);
 if(a%2n===1n)return null;
 if(a===d+2n)return drainB(0n,a,2n);
 if(d%2n===1n)return drainB(d+4n-a,a-1n,3n);
 const x=evalA(d+1n-a,a,2n*a+5n);
 return x===null?null:drainB(...x);
}

// Exact original left-even newAffineCone budget, without computing 3^p
// where the exponent p may be astronomical.
function coneLE(a,d){
 if(d%2n!==0n||a<d+3n)return false;
 let minExponent=0;
 while(tau(minExponent)<d+2n)minExponent++;
 return a-d-2n>=BigInt(minExponent);
}

function window(a,d){
 const p=a>d?a-d:d-a,q=a>d?d:a,S=a+d;
 const gamma=a>d?(d%2n===0n?10n:18n):(d%2n===0n?4n:2n);
 let ell=0;while(tau(ell)<S+3n)ell++;
 const B=34n*BigInt(ell)+122n;
 let k=0,j=0;while(pow3(k)<=B)k++;while(pow3(j)<=B**3n)j++;
 const n=j-k-4,P=pow3(k+2),M=pow3(n),N=M/3n;
 check(n>=3,'window too short');
 const X=2n*(p-3n*q)-gamma,Y=6n*q;
 const x=mod(floor(X,P),M),y=mod(floor(Y,P),M);
 const A=mod(x-3n*y,M),C=mod(4n*x+3n*y,M);
 const U=y%N,V=mod(x+y,N);
 const good=A>=4n&&A<=M-3n&&C>=2n&&C<=M-8n&&
    U>=1n&&U<=N-2n&&V>=1n&&V<=N-3n;
 return {ell,k,j,P,M,N,x,y,A,C,U,V,good,p,q};
}
for(let ell=30;ell<=100;ell++){
 const B=34n*BigInt(ell)+122n;
 let k=0,j=0;while(pow3(k)<=B)k++;while(pow3(j)<=B**3n)j++;
 const P=pow3(k+2),M=pow3(j-k-4),N=M/3n,H=P*N,sigma=(P-1n)/2n;

 // c: t=1 modulo 3, and parity makes c integer.
 const t0=sigma%2n===1n?1n:4n,c0=(H*t0+sigma)/2n;
 const cmin=pow3(ell-5);
 const h=c0>=cmin?0n:ceil(cmin-c0,3n*H);
 const t=t0+6n*h,c=(H*t+sigma)/2n;
 check(c>=cmin&&c<pow3(ell-4),'c interval at ell '+ell);

 // q: input window Y/P=1 modulo M, and q even.
 const u0=M%4n===1n?3n:1n;
 const q0=pow3(k+1)*(1n+M*u0)/2n,G=2n*H;
 const lo=floor(tau(ell-1)-c-3n,5n)+1n;
 const hi=floor(tau(ell)-c-3n*BigInt(ell)-9n,6n);
 const r=q0<lo?ceil(lo-q0,G):0n,q=q0+r*G;
 check(q>0n&&q<=hi&&q%2n===0n&&q>2n*c,'q range at ell '+ell);

 const a=4n*q+c,d=q,out=highLevelNext(a,d);
 check(coneLE(a,d)&&out!==null&&coneLE(out.a,out.d),'cone at ell '+ell);

 const source=window(a,d),target=window(out.a,out.d);
 check(source.ell===ell&&target.ell===ell,'equal mass depth at ell '+ell);
 check(source.k===target.k&&source.j===target.j,'equal window cut at ell '+ell);
 check(source.x===N&&source.y===1n&&source.good,'input sync at ell '+ell);
 check(!target.good&&(target.V===0n||target.V===N-1n),'target failure at ell '+ell);

 const g=source.p-3n*source.q, gp=target.p-3n*target.q;
 const oldh=g-5n,oldhp=gp-5n;
 check(81n*g>4n*source.q,'input linear gap at ell '+ell);
 check(gp<=-2n*target.q,'target linear gap at ell '+ell);
 check(oldh*oldh>5n*source.q,'input square gap at ell '+ell);
 check(oldhp*oldhp>5n*target.q,'target square gap at ell '+ell);

 if([30,40,60,80,100].includes(ell)){
  console.log('ell='+ell,
   'D('+a+','+d+') -> D('+out.a+','+out.d+')',
   'sourceWord=('+source.x+','+source.y+')',
   'targetWord=('+target.x+','+target.y+')',
   'sourceGap/q='+(Number(g)/Number(q)).toPrecision(11),
   'targetAbsGap/q='+(Number(-gp)/Number(target.q)).toPrecision(11),
   'calls='+out.calls);
 }
}
console.log('PASS: all 71 ell=30..100 original-source transitions, equal cuts, linear and square gaps, source sync and target failure');
