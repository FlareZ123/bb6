/* Congruence-guided compression of a closed sparse two-sided DFA invariant.
   Every proposed quotient is re-saturated from blank; any reachable hole,
   state-cap exhaustion, or cost increase rejects the proposal.
   This is an untrusted proof-data search; emit_rungram.py + FastBiDFA certify.
*/
function saturation(table,ds,cap=100000){
 let p=table.replaceAll("_","").match(/.../g).map(m=>m==="---"?-1:12*+m[0]+6*(m[1]==="R")+m.charCodeAt(2)-65);
 let L=ds[0].length/2,R=ds[1].length/2,N=[L,R],E=N.map(n=>Array.from({length:n},()=>new Set())),W=N.map(n=>Array.from({length:n},()=>[])),act=N.map(n=>Array(2*n).fill(-1)),seen=new Set(),todo=[],bad=false;
 E[0][0].add(0);E[1][0].add(0);act[0][0]=act[1][0]=0;
 function add(s,l,r){let id=(s*L+l)*R+r;if(!seen.has(id)){seen.add(id);todo.push([s,l,r]);if(p[s]<0||todo.length>cap)bad=true}}
 function pop(st,e){let [s,l,r]=st,m=p[s],w=m>=12?1:0,n=m%6,b=e&1,x=e>>1;if(m%12>=6)add(2*n+b,ds[0][2*l+w],x);else add(2*n+b,x,ds[1][2*r+w])}
 add(0,0,0);
 for(let i=0;i<todo.length&&!bad;i++){
  let st=todo[i],[s,l,r]=st,m=p[s],w=m>=12?1:0,d=m%12>=6?0:1,x=d?r:l,y=d?l:r,z=ds[d][2*x+w],e=2*x+w;
  act[d][e]=z;
  if(!E[d][z].has(e)){E[d][z].add(e);for(let u of W[d][z]){pop(u,e);if(bad)break}}
  if(bad)break;
  W[1-d][y].push(st);
  for(let e of E[1-d][y]){pop(st,e);if(bad)break}
 }
 let edge_counts=E.map(a=>a.reduce((n,s)=>n+s.size,0));
 return {ok:!bad,states:todo.length,edges:edge_counts[0]+edge_counts[1],edge_counts,summary_counts:N,act,todo,E,dfa:ds};
}
function quotient(active,a,b){
 const n=active.length/2, parent=Array.from({length:n},(_,i)=>i),T=active.slice(),queue=[[a,b]];
 function find(x){while(parent[x]!==x){parent[x]=parent[parent[x]];x=parent[x]}return x}
 for(let k=0;k<queue.length;k++){
  let [x,y]=queue[k].map(find);if(x===y)continue;
  if(x>y)[x,y]=[y,x];parent[y]=x;
  for(let v=0;v<2;v++){let s=T[2*x+v],t=T[2*y+v];if(s<0)T[2*x+v]=t;else if(t>=0)queue.push([s,t])}
 }
 let roots=Array.from({length:n},(_,i)=>i).filter(i=>find(i)===i),idx=new Map(roots.map((x,i)=>[x,i])),res=[];
 for(let x of roots)for(let b=0;b<2;b++){let y=T[2*x+b];res.push(y<0?0:idx.get(find(y)))}
 return res;
}
function prune(s){
 // Delete states absent from the actual fixed point. Every used transition
 // goes to a state with an incoming predecessor. The blank stays at 0.
 let maps=s.E.map(e=>new Map(e.map((x,i)=>x.size?i:-1).filter(i=>i>=0).map((x,i)=>[x,i])));
 return s.act.map((a,d)=>{let res=[];for(let x of maps[d].keys())for(let b=0;b<2;b++){let y=a[2*x+b];res.push(y<0?0:maps[d].get(y))}return res});
}
function score(s){return 2*s.states+3*s.edges+12*s.summary_counts[0]+s.summary_counts[1]}
function candidates(s,d){
 let n=s.summary_counts[d], masks=Array(n).fill(0),ct=Array(n).fill(0),ctx=Array.from({length:n},()=>new Set()),out=[];
 for(let [q,l,r] of s.todo){let x=d?r:l,y=d?l:r;masks[x]|=1<<q;ct[x]++;ctx[x].add(q*1000000+y)}
 for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){
  if((masks[i]&masks[j])===0)continue;
  let overlap=0;for(let a of ctx[i])if(ctx[j].has(a))overlap++;
  let im=(s.act[d][2*i]>=0?1:0)+(s.act[d][2*i+1]>=0?2:0),jm=(s.act[d][2*j]>=0?1:0)+(s.act[d][2*j+1]>=0?2:0);
  let priority=(masks[i]===masks[j]?4:0)+4*overlap/(ct[i]+ct[j])+((im&jm)===0?1:0)-0.001*Math.abs(ct[i]-ct[j]);
  out.push([priority,i,j])
 }
 return out.sort((a,b)=>b[0]-a[0]);
}
function minimize(table,dfa,{attempts=2000,cap=50000}={}){
 let s=saturation(table,dfa,cap);if(!s.ok)throw Error("initial invariant invalid");
 let initial=score(s),tried=0,accepted=0,trace=[];
 while(tried<attempts){
  let best=null;
  for(let d of [1,0]){
   let pairs=candidates(s,d),limit=Math.min(pairs.length,100);
   for(let k=0;k<limit&&tried<attempts;k++){
    let [,a,b]=pairs[k],next=s.dfa.slice();next[d]=quotient(s.act[d],a,b);
    tried++;
    let t=saturation(table,next,Math.min(cap,Math.floor(1.5*s.states)+100));
    if(!t.ok)continue;
    t=saturation(table,prune(t),cap);
    if(!t.ok||score(t)>=score(s))continue;
    if(!best||score(t)<score(best))best=t;
    if(score(t)<0.85*score(s))break;
   }
   if(best)break;
  }
  if(!best)break;
  s=best;accepted++;trace.push([s.states,s.edges,...s.summary_counts,score(s)])
 }
 return {...s,tried,accepted,initial,score:score(s),trace};
}
