'use strict';
// The classifier and small DFA bank below are from Agent47's generate-q0-bank-consume.cjs.
// Discovery only: each emitted leaf must be checked against the original Lean machine semantics.
const moves=Array.from('ABCDEF').flatMap(q=>Array.from('01').flatMap(w=>Array.from('LR').map(d=>w+d+q)));
const dfas=[[[0,0]],[[0,1],[2,1],[2,1]],[[0,1],[2,3],[2,3],[2,3]]];
for(let k of [2,3,4]){const n=2**k;dfas.push(Array.from({length:2*n},(_,i)=>[0,1].map(b=>i<n?2*i+b:n+((2*i+b)%n))));}
function runDFA(cap,mod,depth){const states=[[]],ids=new Map([['',0]]),dfa=[];for(let j=0;j<states.length;j++){const old=states[j];dfa.push([0,1].map(b=>{let s;if(!old.length&&!b)s=[];else if(old.length&&old[0][0]===b)s=[[b,Math.min(cap,old[0][1]+1),(old[0][2]+1)%mod],...old.slice(1)];else s=[[b,1,1%mod],...old.slice(0,depth-1)];let k=JSON.stringify(s);if(!ids.has(k)){ids.set(k,states.length);states.push(s)}return ids.get(k)}))}return dfa;}
const bank=[...dfas];for(const [c,m,d] of [[1,2,1],[1,3,1],[1,4,1],[2,2,1],[2,3,1],[3,1,1],[2,1,2],[3,1,2],[1,2,2],[1,3,2],[2,2,2],[1,4,2],[1,2,3],[2,1,3],[3,2,1],[1,5,1],[1,6,1]])bank.push(runDFA(c,m,d));
const pairs=bank.map((_,i)=>[i,i]);for(let i=0;i<bank.length;i++)for(let j=0;j<bank.length;j++)if(i!==j)pairs.push([i,j]);pairs.sort((a,b)=>bank[a[0]].length*bank[a[1]].length-bank[b[0]].length*bank[b[1]].length);
const specialL=[[0,1],[3,2],[0,4],[0,0],[0,5],[6,2],[0,0]],specialR=[[0,1],[2,3],[4,4],[5,6],[4,4],[7,8],[9,10],[4,4],[4,4],[4,4],[11,12],[4,4],[13,14],[7,4],[9,15],[11,12]];
const li=bank.length;bank.push(specialL,specialR);pairs.push([li,li+1]);
function sourceMitmCert(a,L,R){const ds=[L,R],E=ds.map(d=>d.map(()=>new Set())),W=ds.map(d=>d.map(()=>[])),seen=new Set(),rows=[],nr=R.length,nl=L.length;
 const key=(q,a,l,r)=>((2*q+a)*nl+l)*nr+r;
 function add(q,a,l,r){let k=key(q,a,l,r);if(!seen.has(k)){seen.add(k);rows.push([q,a,l,r]);}}
 function pop(st,e){let [q,a,l,r,n,d,w]=st,b=e%2,i=e>>1;if(d)add(n,b,L[l][w],i);else add(n,b,i,R[r][w]);}
 E[0][0].add(0);E[1][0].add(0);add(0,0,0,0);
 for(let i=0;i<rows.length;i++){let [q,b,l,r]=rows[i],t=a[2*q+b];if(t===24)return null;let w=(t>>1)&1,d=t&1,n=t>>2,st=[q,b,l,r,n,d,w];let old=d?l:r,edge=2*old+w,dest=ds[1-d][old][w],set=E[1-d][dest];if(!set.has(edge)){set.add(edge);for(let waiter of W[1-d][dest])pop(waiter,edge);}let target=d?r:l;W[d][target].push(st);for(let e of E[d][target])pop(st,e);}
 const stack=(d,i)=>({push:d,pop:E[i].map(es=>[...es].map(e=>[e%2,e>>1]))});return {left:stack(L,0),right:stack(R,1),rows};}
const fmt=a=>a.map(x=>moves[x]||'---').join('').match(/.{6}/g).join('_');
function classify(a,limit=256){let l=0n,r=0n,q=0,h=0;const hs=[],mapsR=Array.from({length:6},()=>new Map()),mapsL=Array.from({length:6},()=>new Map());for(let n=0;n<=limit;n++){hs.push(h);for(const d of [1,-1]){const key=d===1?r:(l<<1n)|(r&1n),mp=(d===1?mapsR:mapsL)[q],other=d===1?l:r>>1n;const hist=mp.get(key)||[];for(let j=hist.length-1;j>=0;j--){const [e,eh,eo]=hist[j];if((h-eh)*d<0)continue;let k=0;for(let i=e;i<=n;i++)k=Math.max(k,(eh-hs[i])*d);if(((other^eo)&((1n<<BigInt(k))-1n))===0n)return {kind:'side',d,e,p:n-e,b:eh-d*k};}hist.push([n,h,other]);mp.set(key,hist);}const s=Number(r&1n),i=2*q+s,tr=a[i];if(tr===24)return {kind:'split',n,i};const w=BigInt((tr>>1)&1);if(tr&1){l=(l<<1n)|w;r>>=1n;h++;}else{r=((r>>1n)<<2n)|(w<<1n)|(l&1n);l>>=1n;h--;}q=tr>>2;}return {kind:'open'};}

function scan(table, options={}) {
 const {search,searchPeriodic,known,cap=2000000,ms=Infinity}=options;
 const start=Date.now(),stats={nodes:0,side:0,auto:0,far:0,split:0,last:0,pump:0,open:0,cap:0,bound:0};
 const opens=[],pending=[];
 let processed=0;
 function go(a,f){
  stats.nodes++;
  if(processed>=cap||Date.now()-start>ms){stats.cap++;const t=fmt(a);pending.push(t);return ['c',t];}
  processed++;
  let c=classify(a,128);
  if(c.kind==='open'){
   const t=fmt(a).replaceAll('_','');
   if(known.has(t)){stats.pump++;return ['g',known.get(t)];}
   for(const [l,r] of pairs.slice(0,20))if(sourceMitmCert(a,bank[l],bank[r])){stats.auto++;return ['a',l,r];}
   let far=search(t);if(far){if(far.table!==t)throw Error('FAR table mismatch');stats.far++;return ['f',far];}
   c=classify(a,1500);
   if(c.kind==='open'){
    far=searchPeriodic(t);if(far){if(far.table!==t)throw Error('FAR table mismatch');stats.far++;return ['f',far];}
    for(const [l,r] of pairs.slice(20))if(sourceMitmCert(a,bank[l],bank[r])){stats.auto++;return ['a',l,r];}
   }
  }
  if(c.kind==='side'){stats.side++;return ['s',c.e,c.p,c.d===1,c.b];}
  if(c.kind==='open'){stats.open++;const t=fmt(a);opens.push(t);return ['u',t];}
  stats.bound=Math.max(stats.bound,c.n+6);
  if(a.filter(x=>x===24).length===1){stats.last++;return ['h',c.n,c.i,[]];}
  stats.split++;const kids=[];
  for(let k=0;k<4*Math.min(f+1,6);k++){const b=a.slice();b[c.i]=k;kids.push(go(b,Math.max(f,1+(k>>2))));}
  return ['h',c.n,c.i,kids];
 }
 const a=table.replaceAll('_','').match(/.{3}/g).map(s=>s==='---'?24:moves.indexOf(s));
 if(a.length!==12||a.some(x=>x<0))throw Error('bad partial table');
 const f=Math.max(...a.filter(x=>x<24).map(x=>1+(x>>2)),...a.map((x,i)=>x<24?1+(i>>1):0));
 const tree=go(a,f);
 if(stats.nodes!==stats.side+stats.auto+stats.far+stats.split+stats.last+stats.pump+stats.open+stats.cap)throw Error('census mismatch');
 return {table,stats,opens,pending,tree,complete:!opens.length&&!pending.length,elapsedMs:Date.now()-start,processed};
}
if(require.main===module){
 const fs=require('node:fs'),path=require('node:path'),{search,searchPeriodic}=require('./q0-open-automata.cjs');
 const {verify}=require('./verify-coarse-pumps.cjs');
 const pumps=require('./q0-coarse-pumps.json');for(const c of pumps)verify(c);
 const known=new Map(pumps.map(c=>[c.table,c.root]));
 const route=require('../agent47-raw11-adapter/raw11-route.json');
 const id=Number(process.argv[2]),out=process.argv[3],cap=Number(process.argv[4]||2000000);
 if(![138,140,141,142,143,154].includes(id)||!out||!Number.isSafeInteger(cap)||cap<1)throw Error('usage: q0 id output-dir [node cap]');
 const table=route.targets[id],r=scan(table,{search,searchPeriodic,known,cap});
 fs.mkdirSync(out,{recursive:true});
 const {tree,...summary}=r;summary.id=id;summary.cap=cap;
 fs.writeFileSync(path.join(out,'summary.json'),JSON.stringify(summary,null,2)+'\n');
 fs.writeFileSync(path.join(out,'tree.json'),JSON.stringify(tree));
 console.log(JSON.stringify(summary));
}
module.exports={scan,moves,bank,pairs,sourceMitmCert,classify,fmt};
