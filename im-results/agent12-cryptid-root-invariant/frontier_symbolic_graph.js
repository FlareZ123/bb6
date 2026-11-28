'use strict';
// Eventual affine symbolic token recurrence. A single '*' denotes n.
// Every edge applies above its explicit threshold Q to n=p*q+r.
const V='*';
const C=x=>[0n,BigInt(x)], add=(x,y)=>[x[0]+y[0],x[1]+y[1]],sub=(x,y)=>[x[0]-y[0],x[1]-y[1]],mul=(x,n)=>[x[0]*BigInt(n),x[1]*BigInt(n)],val=(x,n)=>x[0]*n+x[1];
const key=JSON.stringify;
function step(s,p=1n,r=0n){
 let Q=1n,cost=[0n,0n,0n];
 const lift=x=>x===V?[p,r]:C(x), arr=A=>A.map(([v,n])=>[lift(v),lift(n)]);
 function sign(x){let [a,b]=x;if(!a)return b>0n?1:b<0n?-1:0;let sg=a>0n?1:-1;if(val(x,Q)*BigInt(sg)<=0n){let q=(-b)/a+1n;if(q>Q)Q=q;if(val(x,Q)*BigInt(sg)<=0n)throw Error('threshold');}return sg}
 const eq=(x,y)=>sign(sub(x,y))===0, gt=(x,y)=>sign(sub(x,y))>0;
 function time(x){cost[1]+=x[0];cost[2]+=x[1]}
 function product(x,y,n=1n){cost[0]+=n*x[0]*y[0];cost[1]+=n*(x[0]*y[1]+x[1]*y[0]);cost[2]+=n*x[1]*y[1]}
 function div3(x){if(x[0]%3n!==0n)throw {split:true};let b=(x[1]%3n+3n)%3n;return [[x[0]/3n,(x[1]-b)/3n],C(b)]}
 function push(A,v,n=C(1)){let sg=sign(n);if(sg===0)return;if(sg<0)throw Error('negative count');if(A.length&&eq(A[0][0],v))A[0]=[v,add(A[0][1],n)];else A.unshift([v,n])}
 function pop(A){if(!A.length)return C(0);let [v,n]=A[0];if(eq(n,C(1)))A.shift();else A[0]=[v,sub(n,C(1))];return v}
 function take(A,v){return A.length&&eq(A[0][0],C(v))?A.shift()[1]:C(0)}
 function word(z,v,L){push(L,v);push(L,C(0),z);return L}
 let K=arr(s.K),L=arr(s.L);
 function finish(mode,z,v){
  while(K.length&&eq(K[K.length-1][0],C(0)))K.pop();
  let affine=null;
  function lower(x){if(!x[0]){if(x[1]<0n||x[1]>10000000n)throw {unknown:'constant size'};return Number(x[1])}if(affine)throw {unknown:'multiple slots'};if(x[0]<0n)throw Error('negative slope');if(!gt(x,C(0)))throw Error('nonpositive slot');affine=x;return V}
  let S={mode,K:K.map(([x,n])=>[lower(x),lower(n)]),L:L.map(([x,n])=>[lower(x),lower(n)])};
  if(mode==='EL'){S.z=lower(z);S.v=lower(v)}
  if(!affine)throw {unknown:'lost parameter'};
  return {S,a:affine[0],b:affine[1],p,r,Q,cost}
 }
 function CR(){return finish('CR')}
 function EL(z,v){return finish('EL',z,v)}
 function DR(){return finish('DR')}
 try{
 if(s.mode==='CR'){
  let k=pop(K);if(!gt(k,C(0)))throw Error('invalid CR');
  if(!L.length){if(eq(k,C(1))){time(C(9));return EL(C(1),C(1))}push(K,sub(k,C(2)));time(C(21));return EL(C(2),C(1))}
  if(eq(L[0][0],C(0))){let z=take(L,0);push(K,add(k,mul(z,2)));time(mul(z,2));return CR()}
  let x=pop(L);if(gt(x,C(1))){time(C(2));return {halt:true,p,r,Q,cost}}if(!eq(x,C(1)))throw Error('invalid digit');
  if(!L.length){push(K,k);time(C(33));return EL(C(3),C(1))}
  let y=pop(L);
  if(eq(y,C(0))){push(K,add(k,C(3)));push(K,C(1));time(C(5));return CR()}
  if(eq(y,C(1))){push(K,k);let c=L.length?add(pop(L),C(2)):C(1);time(C(25));return EL(C(2),c)}
  push(K,k);push(K,C(1));push(L,sub(y,C(2)));time(C(15));return DR();
 }
 if(s.mode==='DR'){
  let z=take(L,0);if(L.length){push(L,sub(pop(L),C(1)));push(K,C(1),add(z,C(2)));time(add(mul(z,4),C(3)));return CR()}
  time(add(mul(z,6),C(8)));return EL(add(z,C(1)),C(1));
 }
 if(s.mode!=='EL')throw Error('mode');
 let z=lift(s.z),v=lift(s.v);
 if(!K.length){push(K,C(1));L=word(z,v,L);time(C(1));return CR()}
 let x=pop(K);
 if(eq(v,C(1))&&!L.length){let [q,b]=div3(x);product(q,q,12n);product(add(mul(z,6),C(23)),q);z=add(z,mul(q,4));x=b}
 if(eq(x,C(0))){push(K,add(pop(K),C(1)));L=word(z,v,L);time(C(1));return CR()}
 if(eq(x,C(1))){let n=add(C(1),take(K,1));time(mul(n,2));return EL(add(z,n),v)}
 if(eq(x,C(2))){let n=add(C(1),take(K,2));L=word(sub(z,C(1)),v,L);push(L,C(1),sub(n,C(1)));time(mul(n,7));return EL(C(1),C(1))}
 if(!gt(x,C(2)))throw Error('negative token');push(K,sub(x,C(3)));push(K,C(1),add(z,C(2)));push(L,sub(v,C(1)));time(add(C(8),mul(z,4)));return CR();
 }catch(e){if(e.split)return {split:true};if(e.unknown)return {unknown:e.unknown};throw e}
}
function edges(s){let e=step(s);return e.split?[0n,1n,2n].map(r=>step(s,3n,r)):[e]}
const init={mode:'CR',K:[[1,1]],L:[[0,V],[1,1]]};
const ser=x=>JSON.stringify(x,(_,v)=>typeof v==='bigint'?String(v):v);
function search(limit=1000000,maxD=200,ms=14000){
 const todo=[],seen=new Map([[key(init),{s:init,d:0}]]),start=key(init);let count=0,unknown={},nonunit=0,begin=Date.now();
 function enqueue(d,k){(todo[d]??=[]).push(k)}enqueue(0,start);
 for(let d=0;d<=maxD&&count<limit&&Date.now()-begin<ms;d++){
  let A=todo[d]||[];
  for(let i=0;i<A.length&&count<limit&&Date.now()-begin<ms;i++){
   const k=A[i],n=seen.get(k);if(n.d!==d)continue;count++;
   for(let e of edges(n.s)){
    if(e.unknown){unknown[e.unknown]=(unknown[e.unknown]||0)+1;continue}
    if(e.split)throw Error('nested split');
    if(e.halt){let path=[{from:n.s,...e}],p=k;while(p!==start){let a=seen.get(p);path.unshift({from:seen.get(a.parent).s,...a.e});p=a.parent}return {found:true,d:d+Number(e.p===3n),path,count,seen:seen.size,unknown,nonunit}}
    if(e.a%3n===0n){nonunit++;continue}
    let nd=d+Number(e.p===3n);if(nd>maxD)continue;let t=key(e.S),old=seen.get(t);if(old&&old.d<=nd)continue;
    seen.set(t,{s:e.S,d:nd,parent:k,e});enqueue(nd,t)
   }
  }
  todo[d]=null;
 }
 return {found:false,count,seen:seen.size,unknown,nonunit};
}
module.exports={step,edges,search,init};
if(require.main===module)console.log(ser(search(Number(process.argv[2]||2000000),Number(process.argv[3]||108),Number(process.argv[4]||120000))));
