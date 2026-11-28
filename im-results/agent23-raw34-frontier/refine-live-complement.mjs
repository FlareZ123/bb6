#!/usr/bin/env node
// Exact lazy first-query refinement of the previous accepted Raw34 D1=1RD frontier.
// Numerical discovery only: each non-graph certificate must be checked in original Lean.
import {readFileSync,writeFileSync} from "node:fs";
import {dirname,resolve} from "node:path";
import {fileURLToPath} from "node:url";
function refineFrontier(M,N,D,H,cap=256,maxNodes=200000){
 const check=(x,m)=>{if(!x)throw Error(m)};
 const alphabet=M.alphabet, slots=[7,5,3,1,8,9,10,11], states="ABCDEF";
 const codes=new Map([[null,0],...alphabet.map((a,i)=>[a,i+1])]);
 const base=[21,0,22,0,11,0,16,23,0,0,0,0];
 const slotNum=x=>2*states.indexOf(x[0])+Number(x[1]);
 const pow=Array.from({length:13},(_,i)=>25**i);
 const pop=x=>{let n=0;while(x){n++;x&=x-1}return n};
 const fam=["CDE","CDF","CDEF","BCDE","BCDF","BCDEF","ABCD","ABCDE","ABCDF","ABCDEF"].map(s=>({s,req:[...s].reduce((a,x)=>a|(3<<(2*states.indexOf(x))),0),mask:[...s].reduce((a,x)=>a|(1<<states.indexOf(x)),0)}));
 const full=(1<<fam.length)-1;
 const allowed=Array.from({length:12},(_,slot)=>Array.from({length:26},(_,c)=>fam.reduce((mask,f,i)=>mask|(!(f.req&(1<<slot))||(c>=2&&(f.mask&(1<<((c-2)%6))))?1<<i:0),0)));
 const memo=new Map();
 function graph(mask,fixed){
  if(!mask)return 0;
  if(fam.some((f,i)=>(mask&(1<<i))&&(fixed&f.req)===f.req))return pow[12-pop(fixed)];
  const key=mask*4096+fixed;if(memo.has(key))return memo.get(key);
  let slot=-1,score=-1;
  for(let j=0;j<12;j++)if(!(fixed&(1<<j))){
   const n=fam.filter((f,i)=>(mask&(1<<i))&&(f.req&(1<<j))).length;
   if(n>score){score=n;slot=j}
  }
  check(slot>=0&&score>0,"graph no slot");
  let n=0;for(let c=1;c<=25;c++)n+=graph(mask&allowed[slot][c],fixed|(1<<slot));
  memo.set(key,n);return n;
 }
 function getMF(p){let m=full,f=0;for(let j=0;j<12;j++)if(p[j]){m&=allowed[j][p[j]];f|=1<<j}return[m,f]}
 function sim(p){
  let q=0,h=0,L=0n,R=0n;const hist=[], lm=Array.from({length:6},()=>new Map()),rm=Array.from({length:6},()=>new Map());
  for(let t=0;t<=cap;t++){
   for(const right of [true,false]){
    const map=right?rm[q]:lm[q], key=right?R:L, old=map.get(key);
    if(old)for(let ix=old.length-1;ix>=0;ix--){
     const i=old[ix],o=hist[i],delta=h-o.h;
     if(right?delta<0:delta>0)continue;
     let b=o.h;for(let j=i+1;j<t;j++)b=right?Math.min(b,hist[j].h):Math.max(b,hist[j].h);
     const k=right?o.h-b:b-o.h+1, mask=(1n<<BigInt(k))-1n;
     if(right?((o.L^L)&mask)===0n:((o.R^R)&mask)===0n)return ["side",i,t-i,right,b];
    }
   }
   const slot=2*q+Number(R&1n),a=p[slot];if(a===0)return ["split",slot,t];if(a===1)return ["halt",t];
   hist.push({h,L,R});for(const [map,key] of [[rm[q],R],[lm[q],L]]){let arr=map.get(key);if(!arr)map.set(key,arr=[]);arr.push(t)}
   const c=a-2,w=BigInt(c>=12?1:0),right=(c%12)>=6;q=c%6;
   if(right){L=(L<<1n)|w;R>>=1n;h++}
   else{R=(((R>>1n)<<1n)|w)<<1n| (L&1n);L>>=1n;h--}
  }
  return ["cap",cap];
 }
 const first=Array.from({length:165},()=>[]);for(const x of N.refined)first[x.parentIndex].push(x);
 const key=(i,s,a)=>`${i}/${s}/${a}`;const s1=new Map(N.refined.map(x=>[`${x.parentIndex}/${x.action}`,x.slot]));
 const second=new Map();const add=(k,x)=>{if(!second.has(k))second.set(k,[]);second.get(k).push(x)};
 for(const x of D.all)add(key(x.parentIndex,x.firstSlot,x.firstAction),x);
 for(const x of H.records)add(key(x.sourceParentIndex,s1.get(`${x.sourceParentIndex}/${x.first}`),x.first),x);
 const starts=[];
 for(let i=0;i<165;i++){
  const o=M.open[i],p=base.slice();o.decisions.forEach((a,j)=>{if(a!==null)p[slots[j]]=codes.get(a)});
  for(const x of first[i]){
   if(x.kind==="side"||x.kind==="halt"||(i===68&&x.slot==="F1"&&x.action==="1LD"))continue;
   const a=p.slice();a[slotNum(x.slot)]=codes.get(x.action);
   const dd=second.get(key(i,x.slot,x.action));
   if(!dd)starts.push({source:[i,x.slot,x.action],p:a});
   else for(const y of dd){const kind=y.kind??y.result.kind;if(kind==="side"||kind==="halt")continue;starts.push({source:[i,x.slot,x.action,y.secondSlot??y.nextSlot,y.secondAction??y.second],p:y.codes.slice()})}
  }
 }
 const nodes=[],rows=[],roots=[];let count=0,baseMass=0,maxHalt=0,attainer=null;const stats={},mass={},byC={};
 function addStat(k,m,p){stats[k]=(stats[k]??0)+1;mass[k]=(mass[k]??0)+m;let b=byC[alphabet[p[5]-1]]??={};b[k]=(b[k]??0)+m}
 function visit(p,m,f){
  const idx=nodes.length;nodes.push(null);
  const physical=pow[12-pop(f)],g=graph(m,f),open=physical-g;
  if(!open){nodes[idx]=["graph"];addStat("graph",0,p);return [idx,0]}
  count++;
  const cert=count>maxNodes?["budget"]:sim(p);
  if(cert[0]==="split"){
   const s=cert[1],child=[];check(!p[s],"not fresh");let sum=0;
   for(let a=1;a<=25;a++){p[s]=a;const [j,n]=visit(p,m&allowed[s][a],f|(1<<s));sum+=n;child.push(j)}
   p[s]=0;check(sum===open,"mass split");nodes[idx]=["split",s,child];stats.split=(stats.split??0)+1;return [idx,open]
  }
  nodes[idx]=cert;
  addStat(cert[0],open,p);
  if(cert[0]==="halt"&&cert[1]+1>maxHalt){maxHalt=cert[1]+1;attainer=p.slice()}
  if(cert[0]==="cap"||cert[0]==="budget")rows.push({p:p.slice(),open,cert});
  return [idx,open];
 }
 for(const x of starts){const [m,f]=getMF(x.p);const [id,n]=visit(x.p.slice(),m,f);baseMass+=n;roots.push({...x,id,open:n})}
 check(baseMass===110397542,"input graph complement mismatch "+baseMass);check(Object.values(mass).reduce((a,b)=>a+b,0)===baseMass,"output mismatch");
 return {cap,maxNodes,baseMass,stats,mass,byC,maxHalt,attainer,rows,nodes,roots};
}
const here=dirname(fileURLToPath(import.meta.url));
const files=["D1-1RD-proof-frontier.json","one-step-refine.json","depth2-C1-0RF.json","depth2-highmass-other.json"];
const data=files.map(p=>JSON.parse(readFileSync(resolve(here,p),"utf8")));
const cap=Number(process.argv[2]??256),maxNodes=Number(process.argv[3]??200000);
const r=refineFrontier(...data,cap,maxNodes);
if(process.argv[4])writeFileSync(process.argv[4],JSON.stringify(r)+"\n");
const {rows,nodes,roots,...summary}=r;console.log(JSON.stringify({...summary,rows:rows.length,nodes:nodes.length,roots:roots.length},null,2));
