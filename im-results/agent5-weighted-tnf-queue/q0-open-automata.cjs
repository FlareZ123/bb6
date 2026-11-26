// Primitive forward FAR saturation followed by reverse-NFA subset construction.
// Usage: node q0-open-automata.cjs q0-open-root-scan-2026-11-26.json
const fs=require("node:fs");
function solve(table,k,kind,mirror,limit=100000,cap=2,depth=2){
 const moves=table.match(/.{3}/g).map(t=>t==="---"?null:[+t[0],Number((t[1]==="R")!==mirror),t.charCodeAt(2)-65]);
 const left=[[]],li=new Map([["[]",0]]),delta=new Map(),pred=[],pending=[],nodes=[["T"]],ni=new Map([['["T"]',0]]),edges=[new Set()],copying=[],events=[];
 const node=x=>{let key=JSON.stringify(x);if(!ni.has(key)){ni.set(key,nodes.length);nodes.push(x);edges.push(new Set());}return ni.get(key)};
 const ctrl=(l,q,d)=>node(["c",l,q,d]);
 const add=(s,a,t)=>{let v=2*t+a;if(!edges[s].has(v)){edges[s].add(v);events.push([s,a,t])}};
 const copy=(p,v)=>{const s=copying[v]??=new Set();if(!s.has(p)){s.add(p);for(const e of edges[v])add(p,e%2,e>>1)}};
 const apply=(l,b,q,w,v)=>{let p=ctrl(l,q,0),x=node(["x",p,b]);add(x,w,v);add(p,b,x)};
 const push=(l,a)=>{let key=2*l+a;if(delta.has(key))return delta.get(key);let x=left[l],y;
 // Compress runs of lag-period discrepancies, retaining the last lag bits.
 if(!x.length&&!a)y=[];
 else if(kind.startsWith("blk")){
   // Block alignment is measured from the first nonblank push. Retain
   // partial block and a bounded run history of complete blocks.
   const width=+kind.slice(3),part=x.length?x[0]:[],runs=x.slice(1),ps=[...part,a];
   if(ps.length<width)y=[ps,...runs];
   else {
     const v=ps.reduce((n,b)=>2*n+b,0);
     const rs=runs.length&&runs[0][0]===v
       ?[[v,Math.min(cap,runs[0][1]+1),(runs[0][2]+1)%k],...runs.slice(1)]
       :[[v,1,1%k],...runs.slice(0,depth-1)];
     y=[[],...rs];
   }
 }
 else if(kind.startsWith("lag")){
   const lag=+kind.slice(3),hist=x.length?x[0]:Array(lag).fill(0),runs=x.slice(1),e=Number(a!==hist[lag-1]);
   const ys=runs.length&&runs[0][0]===e
     ?[[e,Math.min(cap,runs[0][1]+1),(runs[0][2]+1)%k],...runs.slice(1)]
     :[[e,1,1%k],...runs.slice(0,depth-1)];
   y=[[a,...hist.slice(0,lag-1)],...ys];
 }
 else if(kind==="ngram")y=[a,...x.slice(0,k-1)];
 else if(x.length&&((kind==="alt")!==(x[0][0]===a)))y=[[a,Math.min(cap,x[0][1]+1),(x[0][2]+1)%k],...x.slice(1)];
 else y=[[a,1,1%k],...x.slice(0,depth-1)];
 let id=JSON.stringify(y);if(!li.has(id)){li.set(id,left.length);left.push(y)}let j=li.get(id);delta.set(key,j);(pred[j]??=[]).push([l,a]);for(const [q,w,v] of pending[j]??[])apply(l,a,q,w,v);return j};
 push(0,0);add(0,0,0);copy(ctrl(0,0,1),0);
 for(let i=0;i<events.length;i++){if(i>=limit)return null;let [s,a,v]=events[i];for(const p of copying[s]??[])add(p,a,v);let [tag,l,q,d]=nodes[s];if(tag!=="c")continue;let m=moves[2*q+a];if(!m)return null;let [w,d2,q2]=m;if(d2)copy(ctrl(push(l,w),q2,1),v);else{(pending[l]??=[]).push([q2,w,v]);for(const [l0,b] of pred[l]??[])apply(l0,b,q2,w,v)}}
 let zero=new Set([0]);for(let change=true;change;){change=false;for(let s=0;s<nodes.length;s++)if(!zero.has(s)&&[...edges[s]].some(e=>e%2===0&&zero.has(e>>1))){zero.add(s);change=true}}
 const R=[zero],rids=new Map([[Array.from(zero).sort((a,b)=>a-b).join(","),0]]),reversePush=new Map();
 for(let r=0;r<R.length;r++){if(r>=2000)return null;for(let a=0;a<2;a++){let y=new Set();for(let s=0;s<nodes.length;s++)if([...edges[s]].some(e=>e%2===a&&R[r].has(e>>1)))y.add(s);let key=[...y].sort((a,b)=>a-b).join(",");if(!rids.has(key)){rids.set(key,R.length);R.push(y)}reversePush.set(2*r+a,rids.get(key))}}
 let nl=left.length,nr=R.length,lp=delta,rp=reversePush;
 const allowed=(q,a,l,r)=>{if(mirror)[l,r]=[r,l];let set=R[reversePush.get(2*r+a)];return [0,1].some(d=>set.has(ni.get(JSON.stringify(["c",l,q,d]))))};
 if(mirror){[nl,nr]=[nr,nl];[lp,rp]=[rp,lp]}
 const pops=(p,n)=>{let a=Array.from({length:n},()=>[]);for(let [x,j] of p)a[j].push([x%2,x>>1]);return a};
 let lpop=pops(lp,nl),rpop=pops(rp,nr),seen=new Set(),todo=[];
 const addrow=(q,a,l,r)=>{let key=((2*q+a)*nl+l)*nr+r;if(!allowed(q,a,l,r))throw Error("closure mismatch "+table);if(!seen.has(key)){seen.add(key);todo.push([q,a,l,r])}};
 addrow(0,0,0,0);
 for(let i=0;i<todo.length;i++){let [q,a,l,r]=todo[i],t=table.slice(6*q+3*a,6*q+3*a+3);if(t==="---")throw Error("open row");let w=+t[0],d=t[1],n=t.charCodeAt(2)-65;if(d==="R"){let j=lp.get(2*l+w);if(j===undefined)throw Error("missing push");for(let [b,r0] of rpop[r])addrow(n,b,j,r0)}else{let j=rp.get(2*r+w);if(j===undefined)throw Error("missing push");for(let [b,l0] of lpop[l])addrow(n,b,l0,j)}}
 let L={pop:lpop,push:Array.from({length:nl},(_,i)=>[lp.get(2*i)??0,lp.get(2*i+1)??0])},RR={pop:rpop,push:Array.from({length:nr},(_,i)=>[rp.get(2*i)??0,rp.get(2*i+1)??0])};
 let mem=(p,a,i)=>p.some(([b,j])=>a===b&&i===j);
 if(!mem(L.pop[0],0,0)||!mem(RR.pop[0],0,0))throw Error("bad seed");
 for(let [q,a,l,r] of todo){let t=table.slice(6*q+3*a,6*q+3*a+3),w=+t[0],n=t.charCodeAt(2)-65;
 if(t[1]==="R"){let j=L.push[l][w];if(!mem(L.pop[j],w,l)||!RR.pop[r].every(([b,k])=>seen.has(((2*n+b)*nl+j)*nr+k)))throw Error("right closure")}
 else{let j=RR.push[r][w];if(!mem(RR.pop[j],w,r)||!L.pop[l].every(([b,k])=>seen.has(((2*n+b)*nl+k)*nr+j)))throw Error("left closure")}}
 return {table,k,kind,mirror,cap,depth,left:L,right:RR,rows:todo};
}
function search(table){for(const [kind,ks] of [["ngram",[1,2,3,4,5,6,7,8]],["run",[2,3,4,5,6,7,8]]])for(const k of ks)for(const mirror of [false,true]){let c=solve(table,k,kind,mirror);if(c)return c}return null}
function emit(c,id){const bit=x=>x?"true":"false";const stack=s=>`⟨#[${s.pop.map(es=>`[${es.map(([b,j])=>`(${bit(b)},${j})`).join(",")}]`).join(",")}],#[${s.push.map(([i,j])=>`(${i},${j})`).join(",")}]⟩`;const trie=xs=>xs.length===0?".empty":xs.length===1&&xs[0]===0?".leaf":`(.branch ${trie(xs.filter(x=>x%2===0).map(x=>x>>1))} ${trie(xs.filter(x=>x%2===1).map(x=>x>>1))})`;let rows=Array.from({length:12},(_,i)=>trie(c.rows.filter(([q,a])=>2*q+a===i).map(([q,a,l,r])=>r+c.right.pop.length*l).sort((a,b)=>a-b)));let cases=c.table.match(/.{3}/g).map((t,i)=>`  | (${i>>1},${bit(i%2)}) => ${t==="---"?"none":`some (some ⟨${bit(t[0]==="1")},${bit(t[1]==="R")},${t.charCodeAt(2)-65}⟩)`}`).join("\n");
return `namespace ${id}\ndef table : PartialMachine := fun s => match s with\n${cases}\n  | _ => none\ndef cert : BB6.Agent4Automata.Cert := ⟨${stack(c.left)}, ${stack(c.right)}, #[${rows.join(",")} ]⟩\ntheorem checked : BB6.Agent4Automata.check table cert = true := by decide\ntheorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=\n  BB6.Agent4Automata.never table cert checked m hm\n#print axioms never\nend ${id}\n`}
const extraDFAs=[[[[0,1],[2,3],[4,5],[6,7],[8,9],[10,5],[11,12],[13,14],[10,5],[10,15],[10,5],[16,17],[18,19],[20,5],[21,22],[23,24],[25,26],[27,28],[29,30],[31,32],[33,34],[35,36],[37,38],[10,5],[10,5],[39,5],[10,40],[41,42],[43,44],[10,5],[10,45],[46,47],[48,49],[10,5],[10,50],[51,52],[53,54],[10,5],[10,5],[55,56],[57,58],[59,60],[61,62],[63,64],[65,66],[67,68],[69,70],[2,3],[71,72],[73,74],[75,76],[77,78],[79,80],[81,82],[83,84],[10,5],[10,5],[10,5],[10,5],[85,5],[10,5],[43,5],[10,5],[10,5],[10,5],[10,5],[10,5],[10,5],[10,5],[85,5],[10,86],[10,5],[10,5],[10,5],[10,5],[10,5],[10,5],[10,5],[10,87],[10,5],[10,5],[10,5],[10,88],[89,90],[91,44],[92,93],[94,95],[96,97],[98,99],[100,101],[102,103],[104,105],[10,5],[10,5],[10,5],[10,5],[10,5],[10,5],[10,5],[10,5],[85,5],[10,106],[107,5],[21,22],[10,5],[10,5],[108,109],[110,111],[10,5],[10,5],[10,5],[10,50]],[[0,1],[2,3],[4,5],[6,7],[8,9],[8,9],[8,9],[10,11],[8,9],[8,9],[12,13],[14,15],[8,9],[8,9],[8,16],[8,17],[18,19],[20,21],[8,9],[8,9],[8,22],[23,24],[25,26],[27,28],[29,30],[8,9],[8,9],[8,9],[8,9],[8,9],[31,11],[32,33],[8,9],[8,9]]],[[[0,1],[2,3],[4,5],[6,7],[8,9],[10,11],[12,9],[12,9],[13,14],[12,9],[15,16],[17,18],[12,9],[19,9],[20,21],[8,9],[10,11],[12,9],[12,9],[22,23],[24,25],[26,27],[19,9],[20,21],[8,9],[10,11],[12,9],[12,9]],[[0,1],[2,3],[4,5],[6,7],[4,5],[4,5],[4,5],[8,9],[10,11],[4,12],[13,14],[13,14],[15,16],[4,5],[4,5],[10,11],[4,12]]]];
function mitmCert(table,L,R){
 const ds=[L,R],E=ds.map(d=>d.map(()=>new Set())),W=ds.map(d=>d.map(()=>[])),seen=new Set(),rows=[],nr=R.length,nl=L.length;
 const key=(q,a,l,r)=>((2*q+a)*nl+l)*nr+r;
 function add(q,a,l,r){let k=key(q,a,l,r);if(!seen.has(k)){seen.add(k);rows.push([q,a,l,r])}}
 function pop(st,e){let [q,a,l,r,n,d,w]=st,b=e%2,i=e>>1;if(d)add(n,b,L[l][w],i);else add(n,b,i,R[r][w])}
 if(L[0][0]!==0||R[0][0]!==0)throw Error("blank push");
 E[0][0].add(0);E[1][0].add(0);add(0,0,0,0);
 for(let i=0;i<rows.length;i++){let [q,a,l,r]=rows[i],t=table.slice(6*q+3*a,6*q+3*a+3);if(t==="---")return null;let w=+t[0],d=Number(t[1]==="R"),n=t.charCodeAt(2)-65,st=[q,a,l,r,n,d,w],old=d?l:r,edge=2*old+w,dest=ds[1-d][old][w];if(!E[1-d][dest].has(edge)){E[1-d][dest].add(edge);for(let waiter of W[1-d][dest])pop(waiter,edge)}let target=d?r:l;W[d][target].push(st);for(let e of E[d][target])pop(st,e)}
 for(let [q,a,l,r] of rows){let t=table.slice(6*q+3*a,6*q+3*a+3),w=+t[0],n=t.charCodeAt(2)-65;if(t[1]==="R"){let j=L[l][w];if(!E[0][j].has(2*l+w)||![...E[1][r]].every(e=>seen.has(key(n,e%2,j,e>>1))))throw Error("right closure")}else{let j=R[r][w];if(!E[1][j].has(2*r+w)||![...E[0][l]].every(e=>seen.has(key(n,e%2,e>>1,j))))throw Error("left closure")}}
 const stack=(d,i)=>({push:d,pop:E[i].map(es=>[...es].map(e=>[e%2,e>>1]))});
 return {table,left:stack(L,0),right:stack(R,1),rows};
}

// Keep the historical search unchanged; extended searches are opt-in.
function searchPeriodic(table){
 let c=search(table);if(c)return c;
 for(const kind of ["ngram","run"])for(const depth of [1,3,4])for(const cap of [1,2,3])for(const k of (kind==="ngram"?[9,10,11]:[2,3,4,5,6]))for(const mirror of [false,true]){
   if(kind==="ngram"&&(depth!==1||cap!==1))continue;
   c=solve(table,k,kind,mirror,100000,cap,depth);if(c)return c;
 }
 for(const depth of [1,2,3])for(const cap of [1,2,3,4])for(const k of [1,2,3,4,5,6,7,8])for(const mirror of [false,true]){
   c=solve(table,k,"alt",mirror,100000,cap,depth);if(c)return c;
 }
 for(const lag of [3,2,4,5,6])for(const depth of [1,2,3])for(const cap of [1,2,3])for(const k of [1,2,3,4,5,6,7,8])for(const mirror of [false,true]){
   c=solve(table,k,"lag"+lag,mirror,100000,cap,depth);if(c)return c;
 }
 for(const width of [3,4,2,5,6,7,8])for(const depth of [1,2,3])for(const cap of [1,2,3])for(const k of [1,2,3,4,5,6])for(const mirror of [false,true]){
   c=solve(table,k,"blk"+width,mirror,100000,cap,depth);if(c)return c;
 }
 return null;
}
module.exports={solve,search,searchPeriodic,emit,mitmCert};
if(require.main===module){
const scan=JSON.parse(fs.readFileSync(process.argv[2],"utf8"));
const certs={};for(const r of scan.results){if(r.index===28)continue;for(let i=0;i<r.openTables.length;i++){let c=search(r.openTables[i].table);if(c)certs[`R${r.index}L${i}`]=c;}}
const r49=scan.results.find(r=>r.index===49);for(const [j,i] of [14,18].entries()){let c=mitmCert(r49.openTables[i].table,...extraDFAs[j]);if(!c)throw Error("primitive MITM failed");certs[`R49L${i}`]={...c,width:2};}
fs.writeFileSync("q0-open-automata.json",JSON.stringify(certs));
fs.writeFileSync("Q0OpenAutomata.lean","import TwoSidedAutomata\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nnamespace BB6.Agent5Q0OpenAutomata\nopen BB6Coverage\n"+Object.entries(certs).map(([id,c])=>emit(c,id)).join("\n")+"\nend BB6.Agent5Q0OpenAutomata\n");

}
