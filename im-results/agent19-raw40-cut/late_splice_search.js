/* Discover one-pump crossing-splice recurrences at late blank frontiers.
   Discovery only: every returned certificate has exact trace and word checks.
   side L means increasing-coordinate right word; side R mirrors coordinates. */
function parseSplice(t){return t.replaceAll("_","").match(/.../g)}
function replaySplice(tr,w,side,n){
 const o=side==="L"?1:-1,t=new Set([...w].flatMap((b,i)=>b==="1"?[o*(i+1)]:[]));
 let h=0,q=0;const edge=new Map(),dep=new Map();
 for(let j=0;j<n;j++){
  const m=tr[2*q+Number(t.has(h))];if(m==="---")return null;
  const d=m[1]==="R"?1:-1;
  if(m[0]==="1")t.add(h);else t.delete(h);q=m.charCodeAt(2)-65;
  const x=o*h,k=Math.min(x,x+o*d);
  edge.set(k,(edge.get(k)||"")+(o*d>0?"R":"L")+q);
  dep.set(x,(dep.get(x)||0)+1);h+=d
 }
 const H=o*h;if([...t].some(x=>o*x<=H))return null;
 const len=Math.max(H,...[...t].map(x=>o*x))-H;
 const word=Array.from({length:len},(_,i)=>t.has(o*(H+i+1))?"1":"0").join("");
 return {h,q,word,edge,dep}
}
function normSplice(w,cuts,h,extra){
 let result=[],fixed="",p=0;
 for(let [a,b] of cuts){a-=h;b-=h;if(!(p<=a&&a<b&&b<=w.length))return null;
  let block=w.slice(a,b);fixed+=w.slice(p,a)+block.repeat(1+extra);let tail="";
  while(fixed&&fixed.at(-1)===block.at(-1)){let x=fixed.at(-1);fixed=fixed.slice(0,-1);tail=x+tail;block=x+block.slice(0,-1)}
  result.push(fixed,block);fixed=tail;p=b
 }
 result.push(fixed+w.slice(p));return JSON.stringify(result)
}
function discoverSplice1(table,options={}){
 const N=options.steps||2000000,K=options.window||64,maxD=options.maxD||256,maxReplay=options.maxReplay||1000;
 const tr=parseSplice(table),a=new Uint8Array(2*N+3),off=N+1,history={L:[],R:[]},last={L:null,R:null};
 let h=0,q=0,lo=0,hi=0,replays=0,candidates=0,snaps=0;
 for(let i=0;i<N;i++){
  let bit=a[off+h],m=tr[2*q+bit];if(m==="---")return {late:{n:i,h,q,bit},replays,candidates,snaps};
  if(q===0&&!bit&&((h===lo&&h<0)||(h===hi&&h>0))){
   const side=h===lo?"L":"R",o=side==="L"?1:-1;
   if(last[side]!==h){
    last[side]=h;snaps++;let w="",end=side==="L"?hi:lo;
    for(let x=h+o;o*(end-x)>=0;x+=o)w+=a[off+x]?"1":"0";
    w=w.replace(/0+$/,"");
    for(let j=history[side].length-1;j>=0;j--){
     const s=history[side][j],d=w.length-s.w.length,sh=o*(h-s.h);
     if(d<0||d>maxD||d>s.w.length||sh>0)continue;
     if(d===0&&w===s.w)return {cert:{table,entry:s.i,entryHead:s.h,period:i-s.i,shift:h-s.h,side,cuts:[],increment:0},replays,candidates,snaps};
     if(d===0)continue;
     let l=0,r=0;while(l<s.w.length&&s.w[l]===w[l])l++;
     while(r<s.w.length&&s.w.at(-1-r)===w.at(-1-r))r++;
     if(l+r<s.w.length)continue;
     let bs=[];for(let b=Math.max(d+1,s.w.length-r);b<=Math.min(l,s.w.length);b++){
      let u=b-d;if(s.w.slice(u,b)!==w.slice(b,b+d)||b-sh>w.length)continue;
      bs.push([u,b])
     }
     if(!bs.length)continue;candidates++;
     if(replays>=maxReplay)continue;replays++;
     const e=replaySplice(tr,s.w,side,i-s.i);
     if(!e||e.q!==0||e.h!==h-s.h||e.word!==w)throw Error("snapshot replay disagreement");
     for(const [u,v] of bs){
      if(e.edge.get(u)!==e.edge.get(v))continue;
      const n0=normSplice(s.w,[[u,v]],0,1),n1=normSplice(w,[[u,v]],sh,0);
      if(!n0||n0!==n1)continue;
      let increment=0;for(let x=u+1;x<=v;x++)increment+=e.dep.get(x)||0;
      return {cert:{table,entry:s.i,entryHead:s.h,period:i-s.i,shift:h-s.h,side,cuts:[[u,v]],increment},start:s.w,finish:w,crossing:e.edge.get(u)||"",replays,candidates,snaps}
     }
    }
    history[side].push({i,h,w});if(history[side].length>K)history[side].shift()
   }
  }
  a[off+h]=m[0]==="1"?1:0;h+=m[1]==="R"?1:-1;q=m.charCodeAt(2)-65;lo=Math.min(lo,h);hi=Math.max(hi,h)
 }
 return {unresolved:true,replays,candidates,snaps,h,q,lo,hi}
}
