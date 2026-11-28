#!/usr/bin/env node
import {readFileSync} from "node:fs";
import {dirname,resolve} from "node:path";
import {fileURLToPath} from "node:url";
function selectWhole(M,N,D,H,cap=300){
 const A=M.alphabet,S="ABCDEF",slots=[7,5,3,1,8,9,10,11],C=new Map([[null,0],...A.map((a,i)=>[a,i+1])]),base=[21,0,22,0,11,0,16,23,0,0,0,0];
 const choice=[1];for(let q=0;q<6;q++)for(let w=0;w<2;w++)for(let d=0;d<2;d++)choice.push(2+q+12*w+6*d);
 const sn=s=>2*S.indexOf(s[0])+Number(s[1]);const key=(i,s,a)=>`${i}/${s}/${a}`;
 const sm=new Map(N.refined.map(x=>[`${x.parentIndex}/${x.action}`,x.slot])),second=new Map();
 function add(k,x){if(!second.has(k))second.set(k,[]);second.get(k).push(x)}
 for(const x of D.all)add(key(x.parentIndex,x.firstSlot,x.firstAction),x);
 for(const x of H.records)add(key(x.sourceParentIndex,sm.get(`${x.sourceParentIndex}/${x.first}`),x.first),x);
 const roots=[];
 for(const x of N.refined){
  const i=x.parentIndex;if(x.kind==="halt"||x.kind==="side"||(i===68&&x.slot==="F1"&&x.action==="1LD"))continue;
  const p=base.slice();M.open[i].decisions.forEach((a,j)=>{if(a!==null)p[slots[j]]=C.get(a)});p[sn(x.slot)]=C.get(x.action);
  const ss=second.get(key(i,x.slot,x.action));
  if(!ss)roots.push({p,source:[i,x.slot,x.action]});
  else for(const y of ss){const k=y.kind??y.result.kind;if(k!=="halt"&&k!=="side")roots.push({p:y.codes,source:[i,x.slot,x.action,y.secondSlot??y.nextSlot,y.secondAction??y.second]})}
 }
 const masks=["CDE","CDF","CDEF","BCDE","BCDF","BCDEF","ABCD","ABCDE","ABCDF","ABCDEF"].map(s=>({req:[...s].reduce((a,x)=>a|(3<<(2*S.indexOf(x))),0),state:[...s].reduce((a,x)=>a|(1<<S.indexOf(x)),0)}));
 const allowed=Array.from({length:12},(_,j)=>Array.from({length:26},(_,a)=>masks.reduce((x,f,i)=>x|(!(f.req&(1<<j))||(a>=2&&(f.state&(1<<((a-2)%6))))?1<<i:0),0)));
 const memo=new Map(),pow=Array.from({length:13},(_,i)=>25**i);const pop=x=>{let n=0;while(x){n++;x&=x-1}return n};
 function graph(m,f){if(!m)return 0;if(masks.some((x,i)=>(m&(1<<i))&&(f&x.req)===x.req))return pow[12-pop(f)];const k=m*4096+f;if(memo.has(k))return memo.get(k);let j=-1,n=-1;for(let s=0;s<12;s++)if(!(f&(1<<s))){let b=masks.filter((x,i)=>(m&(1<<i))&&(x.req&(1<<s))).length;if(b>n){j=s;n=b}}if(n<=0)throw Error("graph");let r=0;for(let a=1;a<=25;a++)r+=graph(m&allowed[j][a],f|(1<<j));memo.set(k,r);return r}
 function graphOpen(p){let m=1023,f=0;for(let j=0;j<12;j++)if(p[j]){m&=allowed[j][p[j]];f|=1<<j}return pow[12-pop(f)]-graph(m,f)}
 for(const r of roots){r.holes=r.p.filter(a=>!a).length;r.open=graphOpen(r.p)}
 roots.sort((a,b)=>b.open-a.open);
 function sim(p){
  let ss=63;while(true){let ns=ss;for(let q=0;q<6;q++)if(ss&(1<<q))for(let b=0;b<2;b++){let c=p[2*q+b];if(c<2||!(ss&(1<<((c-2)%6))))ns&=~(1<<q)}if(ns===ss)break;ss=ns}
  let q=0,h=0,L=0n,R=0n;const hist=[],maps=Array.from({length:12},()=>new Map());
  for(let t=0;t<=cap;t++){
   if(ss&(1<<q))return ["closed",t,Array.from({length:6},(_,i)=>i).filter(i=>ss&(1<<i))];
   for(const right of [true,false]){
    const k=right?R:L,map=maps[q*2+(right?1:0)],old=map.get(k);
    if(old)for(let z=old.length-1;z>=0;z--){let i=old[z],o=hist[i],delta=h-o.h;if(right?delta<0:delta>0)continue;let b=o.h;for(let j=i+1;j<t;j++)b=right?Math.min(b,hist[j].h):Math.max(b,hist[j].h);let n=right?o.h-b:b-o.h+1,m=(1n<<BigInt(n))-1n;if(right?((o.L^L)&m)===0n:((o.R^R)&m)===0n)return ["side",i,t-i,right,b]}
   }
   let s=q*2+Number(R&1n),a=p[s];if(!a)return ["split",s,t];if(a===1)return ["halt",t];
   hist.push({L,R,h});for(const [i,k] of [[q*2,L],[q*2+1,R]]){let arr=maps[i].get(k);if(!arr)maps[i].set(k,arr=[]);arr.push(t)}
   let c=a-2,w=BigInt(c>=12?1:0);q=c%6;
   if(c%12>=6){L=L<<1n|w;R>>=1n;h++}else{R=(((R>>1n)<<1n)|w)<<1n|(L&1n);L>>=1n;h--}
  }return ["cap"];
 }
 function build(p,limit){
  const nodes=[],rows=[],stats={};let bound=0;let att=null;
  function visit(p){if(nodes.length>=limit)throw Error("limit");let i=nodes.length;nodes.push(null);let c=sim(p),k=c[0];
   if(k==="split"&&p.filter(x=>x===0).length===1&&!p.includes(1)){k="last";c=["last",c[1],c[2]]}
   if(k==="split"){const s=c[1],ch=[];for(const a of choice){const b=p.slice();b[s]=a;ch.push(visit(b))}c=["split",s,ch]}
   if(k==="cap")rows.push(p.slice());
   if(k==="halt"||k==="last"){let n=c[k==="halt"?1:2]+1;if(n>bound){bound=n;att=p.slice();if(k==="last")att[c[1]]=1}}
   stats[k]=(stats[k]??0)+1;nodes[i]=c;return i
  }
  try{visit(p);return{nodes,rows,stats,bound,att}}catch(e){if(String(e).includes("limit"))return null;throw e}
 }
 const good=[],failed=[];let tested=0;
 for(const root of roots){
  if(root.open<=0||root.holes>4)continue;
  tested++;
  let b=build(root.p,1600);if(b&&!b.rows.length){good.push({...root,...b});if(good.length===6)break}
  else if(b)failed.push({p:root.p,source:root.source,open:root.open,rows:b.rows.length,stats:b.stats});
  if(tested>=200)break;
 }
 return{good,failed:failed.slice(0,8),tested,largest:roots.slice(0,10).map(x=>({p:x.p,open:x.open,holes:x.holes,source:x.source})),roots:roots.length};
}
const dir=dirname(fileURLToPath(import.meta.url));const files=["D1-1RD-proof-frontier.json","one-step-refine.json","depth2-C1-0RF.json","depth2-highmass-other.json"];
const data=files.map(p=>JSON.parse(readFileSync(resolve(dir,p),"utf8")));console.log(JSON.stringify(selectWhole(...data,300)));
