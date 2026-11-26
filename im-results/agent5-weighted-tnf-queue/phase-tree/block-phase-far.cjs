"use strict";
// Heuristic block FAR discovery, followed by direct primitive closure.
// The block layer is untrusted: only the returned single-cell certificate is used.
const {mitmCert}=require("../q0-open-automata.cjs");
function blockFAR(table,width,k,kind,mirror=false,cap=1,depth=2,limit=60000){
 const N=2**width, moves=table.match(/.{3}/g).map(t=>t==="---"?null:[+t[0],Number((t[1]==="R")!==mirror),t.charCodeAt(2)-65]);
 const mac=new Map();
 function macro(q,d,a){
  const key=(2*q+d)*N+a;
  if(mac.has(key))return mac.get(key);
  let h=d?0:width-1,seen=new Set();
  while(h>=0&&h<width){let s=(q*width+h)*N+a;if(seen.has(s)){mac.set(key,null);return null}seen.add(s);let m=moves[2*q+((a>>h)&1)];if(!m){mac.set(key,null);return null}let [w,d2,q2]=m;a=(a&~(1<<h))|(w<<h);q=q2;d=d2;h+=d?1:-1}
  const v=[q,d,a];mac.set(key,v);return v
 }
 const left=[[]],li=new Map([["[]",0]]),delta=new Map(),pred=[],pending=[],nodes=[["T"]],ni=new Map([['["T"]',0]]),edges=[new Set()],copying=[],events=[];
 const node=x=>{let key=JSON.stringify(x);if(!ni.has(key)){ni.set(key,nodes.length);nodes.push(x);edges.push(new Set())}return ni.get(key)};
 const ctrl=(l,q,d)=>node(["c",l,q,d]);
 const add=(s,a,t)=>{let v=N*t+a;if(!edges[s].has(v)){edges[s].add(v);events.push([s,a,t])}};
 const copy=(p,v)=>{const s=copying[v]??=new Set();if(!s.has(p)){s.add(p);for(const e of edges[v])add(p,e%N,Math.floor(e/N))}};
 const apply=(l,b,q,w,v)=>{let p=ctrl(l,q,0),x=node(["x",p,b]);add(x,w,v);add(p,b,x)};
 const push=(l,a)=>{
  const key=N*l+a;if(delta.has(key))return delta.get(key);
  let x=left[l],y;
  if(!x.length&&!a)y=[];else if(kind==="ngram")y=[a,...x.slice(0,k-1)];
  else if(x.length&&x[0][0]===a)y=[[a,Math.min(cap,x[0][1]+1),(x[0][2]+1)%k],...x.slice(1)];
  else y=[[a,1,1%k],...x.slice(0,depth-1)];
  let id=JSON.stringify(y);if(!li.has(id)){li.set(id,left.length);left.push(y)}
  let j=li.get(id);delta.set(key,j);(pred[j]??=[]).push([l,a]);for(const [q,w,v] of pending[j]??[])apply(l,a,q,w,v);return j
 };
 push(0,0);add(0,0,0);copy(ctrl(0,0,1),0);
 for(let i=0;i<events.length;i++){
  if(i>=limit)return null;
  let [s,a,v]=events[i];for(const p of copying[s]??[])add(p,a,v);
  let [tag,l,q,d]=nodes[s];if(tag!=="c")continue;
  let m=macro(q,d,a);if(!m)return null;let [q2,d2,w]=m;
  if(d2)copy(ctrl(push(l,w),q2,1),v);
  else{(pending[l]??=[]).push([q2,w,v]);for(const [l0,b] of pred[l]??[])apply(l0,b,q2,w,v)}
 }
 // Reverse-NFA determinization, with all-zero-tail accepting states.
 let rev=Array.from({length:N},()=>new Map());
 for(let s=0;s<nodes.length;s++)for(const e of edges[s]){
  let a=e%N,t=Math.floor(e/N);if(!rev[a].has(t))rev[a].set(t,[]);rev[a].get(t).push(s)
 }
 let zero=new Set([0]);for(let s of zero)for(let t of rev[0].get(s)??[])zero.add(t);
 const key=x=>[...x].sort((a,b)=>a-b).join(",");
 const R=[zero],rids=new Map([[key(zero),0]]),rp=new Map();
 for(let r=0;r<R.length;r++){
  if(r>=10000)return null;
  for(let a=0;a<N;a++){let y=new Set();for(let t of R[r])for(let s of rev[a].get(t)??[])y.add(s);
   let id=key(y);if(!rids.has(id)){rids.set(id,R.length);R.push(y)}rp.set(N*r+a,rids.get(id))
  }
 }
 // General phase lift: phase j is the block-DFA state after discarding
 // j nearest bits. The pending nearest width-1 bits determine the new block.
 function lift(p,n,reverse){
  let start=[Array(width).fill(0),0],ss=[start],ids=new Map([[JSON.stringify(start),0]]),out=[];
  for(let i=0;i<ss.length;i++){
   if(i>=100000)return null;
   let [phases,tail]=ss[i],row=[];
   for(let a=0;a<2;a++){
    let b=(tail<<1)|a,sym=reverse?b:Number.parseInt(b.toString(2).padStart(width,"0").split("").reverse().join(""),2);
    let x=[[p.get(N*phases.at(-1)+sym)??n,...phases.slice(0,-1)],b&((1<<(width-1))-1)],id=JSON.stringify(x);
    if(!ids.has(id)){ids.set(id,ss.length);ss.push(x)}row.push(ids.get(id))
   }out.push(row)
  }return out
 }
 const L=lift(delta,left.length,false),RR=lift(rp,R.length,true);
 if(!L||!RR)return null;
 return mitmCert(table,...(mirror?[RR,L]:[L,RR]))
}
module.exports={blockFAR};
if(require.main===module){
 const [table,width,k,kind,mirror="false",cap="1",depth="2"]=process.argv.slice(2);
 const result=blockFAR(table,+width,+k,kind,mirror==="true",+cap,+depth);
 if(!result)throw Error("no finite primitive certificate");
 process.stdout.write(JSON.stringify(result)+"\n")
}
