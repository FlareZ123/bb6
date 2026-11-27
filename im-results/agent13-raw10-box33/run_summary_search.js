// Adapted from Agent40's run-summary two-sided closure, for exact box33 tables.
function discover(m,lp,rp,cap=40000){
 const sides=[lp,rp].map(params=>{const [k,c0,c1,p0,p1,lag]=params.length===4?[params[0],params[1],params[1],params[2],params[2],params[3]]:params;const c=[c0,c1],p=[p0,p1];const tab=[{hist:0,bit:0,runs:[]}],ids=new Map([["0/0/",0]]),delta=[[-1,-1]],edges=[[[0,0]]],wait=[[]];return {k,c,p,lag,tab,ids,delta,edges,wait}});
 function push(d,i,b){let s=sides[d],j=s.delta[i][b];if(j>=0)return j;const v=s.tab[i];if(i===0&&b===0)return s.delta[i][b]=0;const h=Math.max(1,s.lag),bit=s.lag?b^((v.hist>>(h-1))&1):b,hist=((v.hist<<1)|b)&((1<<h)-1);let runs=v.runs.slice();if(!runs.length||bit!==v.bit)runs=[1,...runs].slice(0,s.k);else{let n=runs[0]+1;runs[0]=n>=s.c[bit]+s.p[bit]?s.c[bit]:n}const key=hist+"/"+bit+"/"+runs.join(",");j=s.ids.get(key);if(j===undefined){j=s.tab.length;s.ids.set(key,j);s.tab.push({hist,bit,runs});s.delta.push([-1,-1]);s.edges.push([]);s.wait.push([])}return s.delta[i][b]=j}
 let seen=new Set(["0,0,0,0"]),todo=[[0,0,0,0]],failure=false;
 function add(q,a,l,r){if(m[2*q+a]<=0||todo.length>=cap){failure=true;return}let key=[q,a,l,r].join(",");if(!seen.has(key)){seen.add(key);todo.push([q,a,l,r])}}
 function pop(st,e,j){let [q,a,l,r]=st,v=m[q*2+a]-1,n=v>>2,[b,i]=e;if(v&1)add(n,b,j,i);else add(n,b,i,j)}
 for(let t=0;t<todo.length&&!failure;t++){let st=todo[t],[q,a,l,r]=st,v=m[q*2+a]-1,w=v>>1&1,d=v&1?0:1,old=d?r:l,x=d?l:r,j=push(d,old,w),s=sides[d],o=sides[1-d];if(!s.edges[j].some(([b,i])=>b===w&&i===old)){let e=[w,old];s.edges[j].push(e);for(const [st2,j2] of s.wait[j]){pop(st2,e,j2);if(failure)break}}if(failure)break;o.wait[x].push([st,j]);for(const e of o.edges[x]){pop(st,e,j);if(failure)break}}
 if(failure)return null;
 return {lp,rp,L:sides[0].delta.map(x=>x.map(y=>Math.max(0,y))),R:sides[1].delta.map(x=>x.map(y=>Math.max(0,y))),count:todo.length}
}

// Quotient the discovered relation, not the whole language of arbitrary tapes.
// Unused pushes can be set to blank; each quotient is re-saturated.
function closure(m,L,R){
 const dfa=[L,R],edges=dfa.map(x=>x.map(()=>[])),wait=dfa.map(x=>x.map(()=>[]));
 edges[0][0].push([0,0]);edges[1][0].push([0,0]);
 let seen=new Set(["0,0,0,0"]),states=[[0,0,0,0]];
 function add(q,a,l,r){if(m[2*q+a]<=0)throw Error("undefined or halt in closure");const key=[q,a,l,r].join(",");if(!seen.has(key)){seen.add(key);states.push([q,a,l,r])}}
 function pop(st,b,i){const [q,a,l,r]=st,v=m[2*q+a]-1,w=v>>1&1,n=v>>2;if(v&1)add(n,b,L[l][w],i);else add(n,b,i,R[r][w])}
 for(let t=0;t<states.length;t++){const st=states[t],[q,a,l,r]=st,v=m[2*q+a]-1,d=v&1?0:1,w=v>>1&1,old=d?r:l,x=d?l:r,j=dfa[d][old][w];if(!edges[d][j].some(([b,i])=>b===w&&i===old)){edges[d][j].push([w,old]);for(const st2 of wait[d][j])pop(st2,w,old)}wait[1-d][x].push(st);for(const [b,i] of edges[1-d][x])pop(st,b,i)}
 return {states,edges}
}
function classes(keys){const mp=new Map();return keys.map(k=>{if(!mp.has(k))mp.set(k,mp.size);return mp.get(k)})}
function refine(dfa,labels){let c=classes(labels);while(true){let n=classes(dfa.map((r,i)=>[c[i],c[r[0]],c[r[1]]].join(",")));if(n.every((v,i)=>v===c[i]))break;c=n}let out=[];dfa.forEach((r,i)=>out[c[i]]=[c[r[0]],c[r[1]]]);return [out,c]}
function compress(m,L,R){
 let history=[];
 while(true){
  const {states,edges}=closure(m,L,R);history.push([L.length,R.length,states.length]);
  const [l,r]=[L,R].map((D,s)=>{let U=new Map();edges[s].forEach((E,j)=>E.forEach(([b,i])=>U.set(i*2+b,j)));return D.map((_,i)=>[U.get(2*i)??0,U.get(2*i+1)??0])});
  let rows=l.map(()=>[]);states.forEach(([q,a,x,y])=>rows[x].push([q,a,y].join(",")));
  const [nl,lc]=refine(l,rows.map(v=>[...new Set(v)].sort().join(";")));
  rows=r.map(()=>[]);states.forEach(([q,a,x,y])=>rows[y].push([q,a,lc[x]].join(",")));
  const [nr]=refine(r,rows.map(v=>[...new Set(v)].sort().join(";")));
  const C=closure(m,nl,nr),stop=nl.length===L.length&&nr.length===R.length;
  L=nl;R=nr;if(stop)return {L,R,count:C.states.length,history};
 }
}
module.exports={discover,closure,compress};
