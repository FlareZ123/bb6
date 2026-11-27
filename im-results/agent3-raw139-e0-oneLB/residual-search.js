
/* Untrusted exact candidate search; no theorem follows without source checking. */
function block(p,width,cap,mod,runs,flip,phase,limit=50000,keyFn=null){
 const alpha=2**width, macros=new Map(),left=[[]],li=new Map([["[]",0]]),delta=new Map(),pred=[[]],pend=[new Set()],nodes=[["T"]],ni=new Map([["T",0]]),edges=[new Set()],copier=[new Set()],event=[];
 function macro(q,d,a){let key=(q*2+d)*alpha+a;if(macros.has(key))return macros.get(key);let h=d?0:width-1,seen=new Set();while(h>=0&&h<width){let k=(q*width+h)*alpha+a;if(seen.has(k)){macros.set(key,null);return null}seen.add(k);let v=p[2*q+((a>>h)&1)];if(v===24){macros.set(key,null);return null}a=(a&~(1<<h))|(((v>>1)&1)<<h);d=(v&1)^Number(flip);q=v>>2;h+=d?1:-1}let m=[q,d,a];macros.set(key,m);return m}
 function node(k){let s=k.join(",");if(ni.has(s))return ni.get(s);let j=nodes.length;ni.set(s,j);nodes.push(k);edges.push(new Set());copier.push(new Set());return j}
 function ctrl(l,q,d){return node(["c",l,q,d])}
 function add(s,a,t){let k=t*alpha+a;if(!edges[s].has(k)){edges[s].add(k);event.push([s,a,t])}}
 function copy(q,v){if(!copier[v].has(q)){copier[v].add(q);for(let k of [...edges[v]])add(q,k%alpha,Math.floor(k/alpha))}}
 function apply(l,b,q,w,v){let p=ctrl(l,q,0),x=node(["x",p,b]);add(x,w,v);add(p,b,x)}
 function push(l,a){let k=l*alpha+a;if(delta.has(k))return delta.get(k);let xs=left[l],ys;if(keyFn)ys=keyFn(xs,a);else if(!xs.length&&!a)ys=[];else if(phase)ys=[[a,...(xs.length?xs[0].slice(0,runs-1):[])],((xs.length?xs[1]:0)+1)%mod];else if(xs.length&&xs[0][0]===a){let [s,n,m]=xs[0];ys=[[s,Math.min(cap,n+1),(m+1)%mod],...xs.slice(1)]}else ys=[[a,1,1%mod],...xs.slice(0,runs-1)];let str=JSON.stringify(ys);let j=li.get(str);if(j===undefined){j=left.length;li.set(str,j);left.push(ys);pred.push([]);pend.push(new Set())}delta.set(k,j);pred[j].push([l,a]);for(let key of pend[j]){let v=Math.floor(key/(6*alpha)),rem=key%(6*alpha),q=Math.floor(rem/alpha),w=rem%alpha;apply(l,a,q,w,v)}return j}
 push(0,0);add(0,0,0);copy(ctrl(0,0,1),0);
 for(let i=0;i<event.length;i++){if(i>=limit)return null;let [s,a,v]=event[i];for(let q of [...copier[s]])add(q,a,v);let k=nodes[s];if(k[0]!=="c")continue;let [,l,q,d]=k,m=macro(q,d,a);if(!m)return null;let [q2,d2,w]=m;if(d2)copy(ctrl(push(l,w),q2,1),v);else{let key=(v*6+q2)*alpha+w;if(!pend[l].has(key)){pend[l].add(key);for(let [l0,b] of pred[l])apply(l0,b,q2,w,v)}}}
 return [left.length,nodes.length,event.length]
}
const quick=[];
for(let w of [2,3,4,5,6,7,8,1])for(let flip of [false,true])for(let [c,m,r,ph] of [[1,1,1,false],[1,1,2,false],[1,2,1,false],[1,2,2,false],[1,3,2,false],[1,1,2,true],[1,1,3,true],[1,2,3,false],[2,1,2,false],[1,1,4,true],[1,1,3,false],[1,3,3,false],[2,2,2,false],[1,5,2,false],[1,1,5,true],[1,1,6,true],[1,2,4,false],[1,3,4,false],[1,5,4,false],[2,1,3,false]])quick.push([w,c,m,r,flip,ph]);
function step(p,z){let {q,h,l,r,n}=z,s=2*q+Number(l&1n),v=p[s];if(v===24)return null;let w=BigInt((v>>1)&1);return {q:v>>2,h:h+(v&1?1:-1),l:v&1?(r&1n)|(w<<1n)|((l>>1n)<<2n):l>>1n,r:v&1?r>>1n:w|(r<<1n),n:n+1}}
function prefix(p,limit){let z={q:0,h:0,l:0n,r:0n,n:0};for(let i=0;i<limit;i++){let x=step(p,z);if(!x)break;z=x}return z}
function walk(p,limit=100000,z0={q:0,h:0,l:0n,r:0n,n:0},window=32){
 let z=z0,mask=(1n<<BigInt(window))-1n,mr=new Map(),ml=new Map(),heads=[];
 for(let i=0;i<=limit;i++){let {q,h,l,r,n}=z,s=2*q+Number(l&1n);if(p[s]===24)return ['last',n,s];
  heads.push(h);
  let kr=q+':'+(l&mask)+':'+r,kl=q+':'+l+':'+(r&mask);
  let a=mr.get(kr);if(a!==undefined&&h>=heads[a]){let lo=h;for(let j=a;j<i;j++)lo=Math.min(lo,heads[j]);if(heads[a]-lo<window)return ['cycle',z0.n+a,i-a,true,lo]}
  a=ml.get(kl);if(a!==undefined&&h<=heads[a]){let hi=h;for(let j=a;j<i;j++)hi=Math.max(hi,heads[j]);if(hi-heads[a]<=window)return ['cycle',z0.n+a,i-a,false,hi]}
  mr.set(kr,i);ml.set(kl,i);
  if(mr.size>30000)mr.clear();if(ml.size>30000)ml.clear();
  if(i===limit)break;z=step(p,z)
 }
 return ['open',z.n,z.q,z.h,z.l.toString(2).length,z.r.toString(2).length]
}
function splitSearch(row,limit=40000){let p=row.table,z=prefix(p,row.query[0]);if(z.n!==row.query[0]||p[2*z.q+Number(z.l&1n)]!==24||2*z.q+Number(z.l&1n)!==row.query[1])throw Error('query mismatch');
 let kids=[];for(let v=0;v<24;v++){let t=p.slice();t[row.query[1]]=v;let w=walk(t,limit,z,32);if(w[0]==='open'){let a=quick.find(r=>block(t,...r,25000));if(a)w=['wide',...a]}kids.push({v,table:t,w})}return kids}
