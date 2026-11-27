// Adapted from Agent40's run-summary two-sided closure, for exact box33 tables.
function discover(m,lp,rp,cap=40000){
 const sides=[lp,rp].map(([k,c,p,lag])=>{const tab=[{hist:0,bit:0,runs:[]}],ids=new Map([["0/0/",0]]),delta=[[-1,-1]],edges=[[[0,0]]],wait=[[]];return {k,c,p,lag,tab,ids,delta,edges,wait}});
 function push(d,i,b){let s=sides[d],j=s.delta[i][b];if(j>=0)return j;const v=s.tab[i];if(i===0&&b===0)return s.delta[i][b]=0;const h=Math.max(1,s.lag),bit=s.lag?b^((v.hist>>(h-1))&1):b,hist=((v.hist<<1)|b)&((1<<h)-1);let runs=v.runs.slice();if(!runs.length||bit!==v.bit)runs=[1,...runs].slice(0,s.k);else{let n=runs[0]+1;runs[0]=n>=s.c+s.p?s.c:n}const key=hist+"/"+bit+"/"+runs.join(",");j=s.ids.get(key);if(j===undefined){j=s.tab.length;s.ids.set(key,j);s.tab.push({hist,bit,runs});s.delta.push([-1,-1]);s.edges.push([]);s.wait.push([])}return s.delta[i][b]=j}
 let seen=new Set(["0,0,0,0"]),todo=[[0,0,0,0]],failure=false;
 function add(q,a,l,r){if(m[2*q+a]===0||todo.length>=cap){failure=true;return}let key=[q,a,l,r].join(",");if(!seen.has(key)){seen.add(key);todo.push([q,a,l,r])}}
 function pop(st,e,j){let [q,a,l,r]=st,v=m[q*2+a]-1,n=v>>2,[b,i]=e;if(v&1)add(n,b,j,i);else add(n,b,i,j)}
 for(let t=0;t<todo.length&&!failure;t++){let st=todo[t],[q,a,l,r]=st,v=m[q*2+a]-1,w=v>>1&1,d=v&1?0:1,old=d?r:l,x=d?l:r,j=push(d,old,w),s=sides[d],o=sides[1-d];if(!s.edges[j].some(([b,i])=>b===w&&i===old)){let e=[w,old];s.edges[j].push(e);for(const [st2,j2] of s.wait[j]){pop(st2,e,j2);if(failure)break}}if(failure)break;o.wait[x].push([st,j]);for(const e of o.edges[x]){pop(st,e,j);if(failure)break}}
 if(failure)return null;
 return {lp,rp,L:sides[0].delta.map(x=>x.map(y=>Math.max(0,y))),R:sides[1].delta.map(x=>x.map(y=>Math.max(0,y))),count:todo.length}
}
module.exports={discover};
