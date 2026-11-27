'use strict';
// Discovery only: untrusted exact normalized first-hole tree, compatible with Agent5's existing source checker.
function scanShared(table, opts={}) {
 const moves=Array.from('ABCDEF').flatMap(q=>Array.from('01').flatMap(w=>Array.from('LR').map(d=>w+d+q)));
 const parse=s=>s.replaceAll('_','').match(/.{3}/g).map(x=>x==='---'?24:moves.indexOf(x));
 const fmt=a=>a.map(x=>moves[x]||'---').join('').match(/.{6}/g).join('_');
 const a=parse(table), cap=opts.cap??2000000, first=opts.first??128, limit=opts.limit??1500;
 if(a.length!==12||a.some(x=>x<0)||first>limit)throw Error('bad input');
 const fresh=a=>Math.max(...a.map((x,i)=>x<24?Math.max(1+(x>>2),1+(i>>1)):0));
 const L=Array.from({length:6},()=>new Map()),R=Array.from({length:6},()=>new Map()),hist=[];
 const stats={nodes:0,side:0,auto:0,far:0,split:0,last:0,pump:0,open:0,cap:0,bound:0};
 const opens=[],pending=[];let processed=0,steps=0,checks=0,peak=0;
 const start=Date.now();
 function push(q,h,l,r,kl){let n=hist.length;hist.push({q,h,l,r,kl});for(const [m,k] of [[L[q],kl],[R[q],r]]){let v=m.get(k);if(!v){v=[];m.set(k,v)}v.push(n)}peak=Math.max(peak,hist.length);}
 function restore(mark){while(hist.length>mark){const n=hist.length-1,{q,kl,r}=hist.pop();for(const [m,k] of [[L[q],kl],[R[q],r]]){let v=m.get(k);if(v.pop()!==n)throw Error('bad stack');if(!v.length)m.delete(k)}}}
 function side(q,h,l,r,kl){let n=hist.length;for(const d of [1,-1]){let v=(d===1?R[q].get(r):L[q].get(kl));if(!v)continue;let other=d===1?l:r>>1n;
 for(let j=v.length-1;j>=0;j--){checks++;let e=v[j],p=hist[e];if((h-p.h)*d<0)continue;let k=Math.max(0,(p.h-h)*d);for(let i=e;i<n;i++)k=Math.max(k,(p.h-hist[i].h)*d);const old=d===1?p.l:p.r>>1n;if(((other^old)&((1n<<BigInt(k))-1n))===0n)return ['s',e,n-e,d===1,p.h-d*k];}}return null;}
 function apply(q,h,l,r,tr){steps++;const w=BigInt((tr>>1)&1);return tr&1?[tr>>2,h+1,(l<<1n)|w,r>>1n]:[tr>>2,h-1,l>>1n,((r>>1n)<<2n)|(w<<1n)|(l&1n)];}
 function accept(t){const k={a:'auto',f:'far',g:'pump'}[t[0]];if(!k)throw Error('bad fallback type');stats[k]++;return t;}
 function go(q,h,l,r,f,holes){stats.nodes++;if(processed>=cap||(opts.ms!==undefined&&Date.now()-start>opts.ms)){stats.cap++;let t=fmt(a);pending.push(t);return ['c',t];}processed++;
 const mark=hist.length;
 try {
  let tried=false;
  for(;;){let n=hist.length;
   if(n>first&&!tried){tried=true;let c=opts.fallbackFirst?.(a.slice());if(c)return accept(c);}
   if(n>limit){let c=opts.fallbackLate?.(a.slice());if(c)return accept(c);stats.open++;let t=fmt(a);opens.push(t);return ['u',t];}
   const kl=(l<<1n)|(r&1n),c=side(q,h,l,r,kl);if(c){stats.side++;return c;}
   push(q,h,l,r,kl);
   const i=2*q+Number(r&1n),tr=a[i];if(tr===24){stats.bound=Math.max(stats.bound,n+6);if(holes===1){stats.last++;return ['h',n,i,[]];}
     stats.split++;const kids=[];for(let j=0;j<4*Math.min(f+1,6);j++){a[i]=j;const [qq,hh,ll,rr]=apply(q,h,l,r,j);kids.push(go(qq,hh,ll,rr,Math.max(f,1+(j>>2)),holes-1));a[i]=24;}return ['h',n,i,kids];}
   [q,h,l,r]=apply(q,h,l,r,tr);
  }
 } finally {restore(mark);}
 }
 const tree=go(0,0,0n,0n,fresh(a),a.filter(x=>x===24).length);
 if(hist.length||L.some(x=>x.size)||R.some(x=>x.size))throw Error('dirty history');
 if(stats.nodes!==stats.side+stats.auto+stats.far+stats.split+stats.last+stats.pump+stats.open+stats.cap)throw Error('census mismatch');
 return {table,stats,opens,pending,tree,complete:!opens.length&&!pending.length,elapsedMs:Date.now()-start,processed,steps,checks,peak};
}
function scanReplay(table,cap,limit){
 const moves=Array.from('ABCDEF').flatMap(q=>Array.from('01').flatMap(w=>Array.from('LR').map(d=>w+d+q)));
 const a=table.replaceAll('_','').match(/.{3}/g).map(s=>s==='---'?24:moves.indexOf(s));const fmt=a=>a.map(x=>moves[x]||'---').join('').match(/.{6}/g).join('_');let nodes=0,steps=0;
 function classify(){let l=0n,r=0n,q=0,h=0;const hs=[],L=Array.from({length:6},()=>new Map()),R=Array.from({length:6},()=>new Map());
 for(let n=0;n<=limit;n++){hs.push(h);for(let d of [1,-1]){const key=d===1?r:(l<<1n)|(r&1n),mp=(d===1?R:L)[q],other=d===1?l:r>>1n,v=mp.get(key)||[];for(let j=v.length-1;j>=0;j--){const [e,eh,eo]=v[j];if((h-eh)*d<0)continue;let k=0;for(let i=e;i<=n;i++)k=Math.max(k,(eh-hs[i])*d);if(((other^eo)&((1n<<BigInt(k))-1n))===0n)return ['s',e,n-e,d===1,eh-d*k];}v.push([n,h,other]);mp.set(key,v);}const i=2*q+Number(r&1n),tr=a[i];if(tr===24)return ['h',n,i,[]];steps++;const w=BigInt((tr>>1)&1);if(tr&1){l=(l<<1n)|w;r>>=1n;h++}else{r=((r>>1n)<<2n)|(w<<1n)|(l&1n);l>>=1n;h--}q=tr>>2;}return ['u',fmt(a)];}
 function go(f,holes){if(nodes>=cap)return ['c',fmt(a)];nodes++;const t=classify();if(t[0]!=='h'||holes===1)return t;for(let j=0;j<4*Math.min(f+1,6);j++){a[t[2]]=j;t[3].push(go(Math.max(f,1+(j>>2)),holes-1));a[t[2]]=24}return t}
 const f=Math.max(...a.map((x,i)=>x<24?Math.max(1+(x>>2),1+(i>>1)):0));const start=Date.now();const tree=go(f,a.filter(x=>x===24).length);return {tree,nodes,steps,elapsedMs:Date.now()-start};
}
if(require.main===module){
 const fs=require('node:fs'),path=require('node:path');
 const id=Number(process.argv[2]),out=process.argv[3],cap=Number(process.argv[4]||2000000);
 const route=require('./raw11-route.json');if(!route.targets[id]||!out||!Number.isSafeInteger(cap)||cap<1)throw Error('usage: node scan-q0-shared-prefix.cjs id outdir [cap] [--side-only]');
 const only=process.argv.includes('--side-only');
 const o={cap,first:128,limit:only?128:1500};
 if(!only){const {bank,pairs,sourceMitmCert,fmt}=require('../agent5-weighted-tnf-queue/scan-q0-coarse-full.cjs');const {search,searchPeriodic}=require('../agent5-weighted-tnf-queue/q0-open-automata.cjs');const {verify}=require('../agent5-weighted-tnf-queue/verify-coarse-pumps.cjs');const pumps=require('../agent5-weighted-tnf-queue/q0-coarse-pumps.json');for(const c of pumps)verify(c);const known=new Map(pumps.map(c=>[c.table,c.root]));
 o.fallbackFirst=a=>{const t=fmt(a).replaceAll('_','');if(known.has(t))return ['g',known.get(t)];for(const [l,r] of pairs.slice(0,20))if(sourceMitmCert(a,bank[l],bank[r]))return ['a',l,r];const far=search(t);if(far){if(far.table!==t)throw Error('FAR table mismatch');return ['f',far]}return null;};
 o.fallbackLate=a=>{const t=fmt(a).replaceAll('_','');const far=searchPeriodic(t);if(far){if(far.table!==t)throw Error('FAR table mismatch');return ['f',far]}for(const [l,r] of pairs.slice(20))if(sourceMitmCert(a,bank[l],bank[r]))return ['a',l,r];return null;};}
 const r=scanShared(route.targets[id],o);const {tree,...summary}=r;summary.id=id;summary.cap=cap;fs.mkdirSync(out,{recursive:true});fs.writeFileSync(path.join(out,'summary.json'),JSON.stringify(summary,null,2)+'\\n');fs.writeFileSync(path.join(out,'tree.json'),JSON.stringify(tree));console.log(JSON.stringify({...summary,opens:summary.opens.length,pending:summary.pending.length}));
}
module.exports={scanShared,scanReplay};
