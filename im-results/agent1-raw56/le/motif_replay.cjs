// Motif-specific deterministic stack summaries. Untrusted discovery/replay.
const fs = require('fs');
function parse(s){return s.replaceAll('_','').match(/.../g).map(v=>v==='---'?-1:12*(+v[0])+6*(v[1]==='R')+(v.charCodeAt(2)-65))}
function targeted({k,groups}){
 const words=[''],ids=new Map([['',0]]),delta=[[-1,-1]];
 const rules=groups.flatMap(([pat,c,m])=>[...new Set(Array.from({length:pat.length},(_,i)=>pat.slice(i)+pat.slice(0,i)))].map(p=>[p.repeat(c+m),p.repeat(c)]));
 function norm(w){for(;;){let changed=false;for(const [a,b] of rules){const i=w.indexOf(a);if(i!==-1){w=w.slice(0,i)+b+w.slice(i+a.length);changed=true;break}}if(!changed)return w.slice(0,k).replace(/0+$/,'')}}
 return {push:(x,b)=>{if(delta[x][b]>=0)return delta[x][b];let w=norm(b+words[x]),j=ids.get(w);if(j===undefined){j=ids.size;ids.set(w,j);words.push(w);delta.push([-1,-1])}delta[x][b]=j;return j},finish:()=>delta.flat().map(x=>Math.max(0,x)),size:()=>words.length};
}
function solve(table,left,right,cap=35000){
 const tr=parse(table),d=[targeted(left),targeted(right)],edges=[new Map(),new Map()],waiting=[new Map(),new Map()],seen=new Set(),todo=[],H=2**24,Q=H*H;let fail=false,limit=false;
 function add(s,l,r){const x=s*Q+l*H+r;if(seen.has(x))return;seen.add(x);todo.push([s,l,r]);if(tr[s]<0)fail=true;if(todo.length>cap||l>=H||r>=H)limit=true}
 function pop(st,e){const [s,l,r]=st,m=tr[s],w=m/12|0,q=m%6,dir=m%12>=6,b=e[0],src=e[1];if(dir)add(2*q+b,d[0].push(l,w),src);else add(2*q+b,src,d[1].push(r,w))}
 function list(m,i){let v=m.get(i);if(!v){v=[];m.set(i,v)}return v}
 for(const e of edges)e.set(0,[[0,0]]);add(0,0,0);
 for(let i=0;i<todo.length&&!fail&&!limit;i++){let st=todo[i];const [s,l,r]=st,m=tr[s],w=m/12|0,side=+(m%12>=6),other=1-side,old=side?l:r,dest=d[other].push(old,w),x=side?r:l,es=list(edges[other],dest);
 if(!es.some(e=>e[0]===w&&e[1]===old)){const e=[w,old];es.push(e);for(const st2 of list(waiting[other],dest)){pop(st2,e);if(fail||limit)break}}
 if(fail||limit)break;list(waiting[side],x).push(st);for(const e of list(edges[side],x)){pop(st,e);if(fail||limit)break}
 }
 return fail||limit?{status:fail?'fail':'cap',states:todo.length}:{status:'ok',dfa:d.map(x=>x.finish()),states:todo.length,edges:edges.reduce((n,x)=>n+[...x.values()].reduce((a,v)=>a+v.length,0),0),params:[left,right]}
}
if(require.main===module){
 const spec=JSON.parse(fs.readFileSync(0,'utf8'));
 const results=spec.map(({id,table,params,states,edges})=>{
   const z=solve(table,...params,Math.max(35000,states+1));
   if(z.status!=='ok'||z.states!==states||z.edges!==edges)throw Error('motif mismatch '+id+' '+JSON.stringify({status:z.status,states:z.states,edges:z.edges}));
   return {id,table,...z};
 });
 process.stdout.write(JSON.stringify(results));
}
module.exports={solve};
