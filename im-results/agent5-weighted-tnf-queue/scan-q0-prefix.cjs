'use strict';
// Discovery-only shared-prefix normalized first-hole scanner.
// A history frame is pushed only after failing both side-cycle tests.
// A child reuses precisely the history before its first newly assigned move.
const {moves,bank,pairs,sourceMitmCert,fmt}=require('./scan-q0-coarse-full.cjs');
function scanPrefix(table,options={}){
 const {search,searchPeriodic,known=new Map(),cap=2000000,ms=Infinity}=options;
 const start=Date.now(),stats={nodes:0,side:0,auto:0,far:0,split:0,last:0,pump:0,open:0,cap:0,bound:0};
 const perf={primitive:0,reusedPrefix:0,rollbacks:0,sidePairs:0};
 const opens=[],pending=[],history=[];
 const mr=Array.from({length:6},()=>new Map()),ml=Array.from({length:6},()=>new Map());
 let processed=0;
 function keys(c){return [c.r,(c.l<<1n)|(c.r&1n)]}
 function checkSide(c){
  const n=history.length,ks=keys(c);
  for(const d of [1,-1]){
   const k=ks[d===1?0:1],m=(d===1?mr:ml)[c.q],other=d===1?c.l:c.r>>1n;
   const hist=m.get(k)||[];
   for(let j=hist.length-1;j>=0;j--){
    const e=hist[j],eh=history[e].h,eo=d===1?history[e].l:history[e].r>>1n;
    if((c.h-eh)*d<0)continue;
    perf.sidePairs++;
    let z=c.h;
    // Query the extrema of the exact head path, including current head.
    if(n-e<=24){for(let i=e;i<n;i++)z=d===1?Math.min(z,history[i].h):Math.max(z,history[i].h);}
    else {
      const k=31-Math.clz32(n-e),v=history[e+(1<<k)-1],u=history[n-1];
      z=d===1?Math.min(z,v.mn[k],u.mn[k]):Math.max(z,v.mx[k],u.mx[k]);
    }
    const kback=(eh-z)*d;
    if(((other^eo)&((1n<<BigInt(kback))-1n))===0n)return {kind:'side',d,e,p:n-e,b:eh-d*kback};
   }
  }
  return null;
 }
 function append(c){
  const n=history.length,[kr,kl]=keys(c),mn=[c.h],mx=[c.h];
  for(let k=1;(1<<k)<=n+1;k++){
    const u=history[n-(1<<(k-1))];mn[k]=Math.min(mn[k-1],u.mn[k-1]);mx[k]=Math.max(mx[k-1],u.mx[k-1]);
  }
  history.push({...c,kr,kl,mn,mx});
  for(const [m,k] of [[mr[c.q],kr],[ml[c.q],kl]]){let a=m.get(k);if(!a)m.set(k,a=[]);a.push(n);}
 }
 function restore(mark){
  while(history.length>mark){
   const u=history.pop(),n=history.length;
   for(const [m,k] of [[mr[u.q],u.kr],[ml[u.q],u.kl]]){
    const a=m.get(k);if(a.pop()!==n)throw Error('bad history stack');if(!a.length)m.delete(k);
   }
   perf.rollbacks++;
  }
 }
 function step(c,tr){
  perf.primitive++;const w=BigInt((tr>>1)&1),q=tr>>2;
  if(tr&1)return {q,l:(c.l<<1n)|w,r:c.r>>1n,h:c.h+1};
  return {q,l:c.l>>1n,r:((c.r>>1n)<<2n)|(w<<1n)|(c.l&1n),h:c.h-1};
 }
 function run(a,c,limit){
  while(history.length<=limit){
   const n=history.length,side=checkSide(c);
   if(side)return side;
   append(c);
   const i=2*c.q+Number(c.r&1n),tr=a[i];
   if(tr===24)return {kind:'split',n,i,c};
   c=step(c,tr);
  }
  return {kind:'open',c};
 }
 function go(a,f,c){
  stats.nodes++;
  if(processed>=cap||Date.now()-start>ms){stats.cap++;const t=fmt(a);pending.push(t);return ['c',t];}
  processed++;const mark=history.length;perf.reusedPrefix+=mark;
  try{
   let v=run(a,c,128);
   if(v.kind==='open'){
    const t=fmt(a).replaceAll('_','');
    if(known.has(t)){stats.pump++;return ['g',known.get(t)];}
    for(const [l,r] of pairs.slice(0,20))if(sourceMitmCert(a,bank[l],bank[r])){stats.auto++;return ['a',l,r];}
    let far=search(t);if(far){if(far.table!==t)throw Error('FAR table mismatch');stats.far++;return ['f',far];}
    v=run(a,v.c,1500);
    if(v.kind==='open'){
     far=searchPeriodic(t);if(far){if(far.table!==t)throw Error('FAR table mismatch');stats.far++;return ['f',far];}
     for(const [l,r] of pairs.slice(20))if(sourceMitmCert(a,bank[l],bank[r])){stats.auto++;return ['a',l,r];}
    }
   }
   if(v.kind==='side'){stats.side++;return ['s',v.e,v.p,v.d===1,v.b];}
   if(v.kind==='open'){stats.open++;const t=fmt(a);opens.push(t);return ['u',t];}
   stats.bound=Math.max(stats.bound,v.n+6);
   if(a.filter(x=>x===24).length===1){stats.last++;return ['h',v.n,v.i,[]];}
   stats.split++;const kids=[];
   for(let k=0;k<4*Math.min(f+1,6);k++){
    const b=a.slice();b[v.i]=k;
    kids.push(go(b,Math.max(f,1+(k>>2)),step(v.c,k)));
   }
   return ['h',v.n,v.i,kids];
  } finally {restore(mark);}
 }
 const a=table.replaceAll('_','').match(/.{3}/g).map(s=>s==='---'?24:moves.indexOf(s));
 if(a.length!==12||a.some(x=>x<0))throw Error('bad partial table');
 const f=Math.max(...a.filter(x=>x<24).map(x=>1+(x>>2)),...a.map((x,i)=>x<24?1+(i>>1):0));
 const tree=go(a,f,{q:0,l:0n,r:0n,h:0});
 if(history.length||mr.some(m=>m.size)||ml.some(m=>m.size))throw Error('unrestored trace');
 if(stats.nodes!==stats.side+stats.auto+stats.far+stats.split+stats.last+stats.pump+stats.open+stats.cap)throw Error('census mismatch');
 return {table,stats,perf,opens,pending,tree,complete:!opens.length&&!pending.length,elapsedMs:Date.now()-start,processed};
}
module.exports={scanPrefix};

