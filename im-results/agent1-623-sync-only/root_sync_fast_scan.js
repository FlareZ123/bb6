#!/usr/bin/env node
// Source-derived, resumable #623 blank-root S-window synchronization scan.
// Usage: node root_sync_fast_scan.js --steps=50000 --out=root50k.json
// Resume: node root_sync_fast_scan.js --from=root50k.json --steps=100000 --out=root100k.json
//
// The initial (index 0..8) transitions use literal upstream highLevelNext
// evalA/drainB. From index 9 onward, source-certified canonical-ray formulas
// evaluate the original transition with the source three-state ternary drain
// transducer from DrainDigitTransducerCarry.lean. Its output-digit statistics
// D=L-2*n2 and R=n1+n2 match original-source transitions.
// This is a FINITE experiment; it proves no all-time root invariant.
const fs=require('fs');
const arg=(key,def=null)=>{
 const entry=process.argv.slice(2).find(z=>z.startsWith('--'+key+'='));
 return entry===undefined?def:entry.slice(key.length+3);
};
const limit=Number(arg('steps','50000'));
const from=arg('from'),out=arg('out');
if(!Number.isSafeInteger(limit)||limit<0)throw Error('bad steps');

const drainTable=[
 [[1,2],[0,1],[2,0]], // carry A
 [[0,0],[1,2],[0,1]], // carry B
 [[0,1],[2,0],[0,2]]  // carry C
];
const gamma=[18n,10n,2n,4n]; // LO LE RO RE, sector determined by d parity
const mod=(a,m)=>(a%m+m)%m;
const floor=(a,m)=>a%m<0n?a/m-1n:a/m;
const powers=[1n];
function p3(k){
 while(powers.length<=k)powers.push(powers[powers.length-1]*3n);
 return powers[k];
}
function runDrainStats(b){
 if(b<1n)throw Error('invalid drain budget');
 const exponent=(2n*b-1n).toString(3).length-1;
 const L=exponent%2===Number(b%2n)?exponent:exponent+1;
 const digits=b.toString(3);
 let state=0,n1=0,n2=0;
 for(let i=0;i<L;i++){
  const d=i<digits.length?digits.charCodeAt(digits.length-i-1)-48:0;
  const [next,output]=drainTable[state][d];
  state=next;
  if(output===1)n1++;
  else if(output===2)n2++;
 }
 return {D:BigInt(L-2*n2),R:BigInt(n1+n2),L};
}
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
 while(b>0n){
  const z=evalA(a,b-1n,d+2n*b+3n);
  if(z===null)return null;
  [a,b,d]=z;
 }
 return [a,d];
}
function originalNext(a,d){
 if(a===0n)return d%2n===1n?drainB(d+1n,2n,2n):[d,7n];
 if(d%2n===1n&&a>=d+5n)return drainB(a-d-5n,d+3n,5n);
 if(d%2n===0n&&a>=d+3n)return drainB(a-d-2n,d+2n,2n);
 if(a%2n===1n)return null;
 if(a===d+2n)return drainB(0n,a,2n);
 if(d%2n===1n)return drainB(d+4n-a,a-1n,3n);
 const z=evalA(d+1n-a,a,2n*a+5n);
 return z===null?null:drainB(...z);
}
function sectorOf(a,d){
 // LO=0 LE=1 RO=2 RE=3. The parity belongs to the d counter,
 // not the a counter (important on RO/RE states).
 return a>d?(d%2n===1n?0:1):(d%2n===1n?2:3);
}
function next(a,d,index){
 if(index<9||a===0n||a===d)return originalNext(a,d);
 const sector=sectorOf(a,d);
 const p=a>d?a-d:d-a,q=a>d?d:a;
 const budgets=[q+3n,q+2n,q-1n,q+1n],b=budgets[sector];
 if(b<1n)return originalNext(a,d);
 const {D,R}=runDrainStats(b);
 const beta=[-D-5n,-D-2n,4n-D,1n-D][sector];
 const delta=[2n*D+2n*R+14n,2n*D+2n*R+8n,
              2n*D+2n*R,2n*D+2n*R+3n][sector];
 const a1=p+beta,d1=3n*q+delta;
 if(a1<0n||d1<0n)return originalNext(a,d);
 return [a1,d1];
}
const saved=from?JSON.parse(fs.readFileSync(from,'utf8')):null;
let a=saved?BigInt(saved.a):0n,d=saved?BigInt(saved.d):7n;
let ell=saved?saved.ell:0,k=saved?saved.k:0,j=saved?saved.j:0;
let checked=saved?saved.checked:0;
let counts=saved?saved.sampled:{};
let start=saved?saved.index:0;
let failed=null;
if(limit<start)throw Error('steps cannot precede checkpoint index');
const began=Date.now();
for(let index=start;index<=limit;index++){
 // A resumed checkpoint already included index=start in its statistics.
 if(index>=33&&!(saved&&index===start)){
  const S=a+d;
  while((p3(ell)-1n)/2n<S+3n)ell++;
  while(ell>0&&(p3(ell-1)-1n)/2n>=S+3n)ell--;
  const B=34n*BigInt(ell)+122n;
  while(p3(k)<=B)k++;
  while(k>0&&p3(k-1)>B)k--;
  while(p3(j)<=B*B*B)j++;
  while(j>0&&p3(j-1)>B*B*B)j--;
  const n=j-k-4;
  if(n>=3){
   const P=p3(k+2),M=p3(n),N=M/3n;
   const p=a>d?a-d:d-a,q=a>d?d:a,s=sectorOf(a,d);
   const X=2n*(p-3n*q)-gamma[s],Y=6n*q;
   const x=mod(floor(X,P),M),y=mod(floor(Y,P),M);
   const A=mod(x-3n*y,M),C=mod(4n*x+3n*y,M);
   const U=y%N,V=mod(x+y,N);
   const good=A>=4n&&A<=M-3n&&C>=2n&&C<=M-8n&&
        U>=1n&&U<=N-2n&&V>=1n&&V<=N-3n;
   checked++;
   counts[n]=(counts[n]||0)+1;
   if(!good){
    failed={index,sector:s,ell,k,j,n,P:String(P),M:String(M),
     x:String(x),y:String(y),A:String(A),C:String(C),
     U:String(U),V:String(V),N:String(N),
     badTests:[A<4n||A>M-3n,C<2n||C>M-8n,
       U<1n||U>N-2n,V<1n||V>N-3n]};
    break;
   }
  }
 }
 if(index===limit)break;
 const z=next(a,d,index);
 if(z===null){failed={index,halting:true};break;}
 [a,d]=z;
}
const reached=failed?failed.index:limit;
const output={source:'original Cryptids highLevelNext prefix and source-certified ternary drain cocycle thereafter',
 index:reached,a:String(a),d:String(d),ell,k,j,checked,failed,
 sampled:counts,elapsed_ms:Date.now()-began,
 original_file:'BusyBeaver/BB6/M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean',
 created_at:new Date().toISOString()};
if(out)fs.writeFileSync(out,JSON.stringify(output,null,2)+'\n');
const stdout={index:output.index,checked,failed,sampled:counts,
 elapsed_ms:output.elapsed_ms,a_bits:a.toString(2).length,d_bits:d.toString(2).length,
 checkpoint:out||null};
console.log(JSON.stringify(stdout,null,2));
if(failed)process.exitCode=2;
