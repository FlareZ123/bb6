function discover(m){

 const sides=[0,1].map(()=>({tab:[{bit:0,runs:[]}],ids:new Map([["0/",0]]),delta:[[-1,-1]],edges:[[[0,0]]],wait:[[]]}));
 function push(d,i,b){let s=sides[d],j=s.delta[i][b];if(j>=0)return j;let v=s.tab[i];if(i===0&&b===0)return s.delta[i][b]=0;let runs=v.runs.slice();if(!runs.length||b!==v.bit)runs=[1,...runs].slice(0,5);else runs[0]=Math.min(runs[0]+1,b?3:5);let key=b+"/"+runs.join(","),id=s.ids.get(key);if(id===undefined){id=s.tab.length;s.ids.set(key,id);s.tab.push({bit:b,runs});s.delta.push([-1,-1]);s.edges.push([]);s.wait.push([])}return s.delta[i][b]=id}
 let seen=new Set(["0,0,0,0"]),todo=[[0,0,0,0]];
 function add(q,a,l,r){if(!m[2*q+a])throw Error("halt");let key=[q,a,l,r].join(",");if(!seen.has(key)){seen.add(key);todo.push([q,a,l,r])}}
 function pop(st,e,j){let [q,a,l,r]=st,v=m[q*2+a]-1,n=v>>2,[b,i]=e;if(v&1)add(n,b,j,i);else add(n,b,i,j)}
 for(let t=0;t<todo.length;t++){let st=todo[t],[q,a,l,r]=st,v=m[q*2+a]-1,w=v>>1&1,d=v&1?0:1,old=d?r:l,x=d?l:r,j=push(d,old,w),s=sides[d],o=sides[1-d];if(!s.edges[j].some(([b,i])=>b===w&&i===old)){let e=[w,old];s.edges[j].push(e);for(const [st2,j2] of s.wait[j])pop(st2,e,j2)}o.wait[x].push([st,j]);for(const e of o.edges[x])pop(st,e,j)}
 return {L:sides[0].delta.map(x=>x.map(y=>Math.max(0,y))),R:sides[1].delta.map(x=>x.map(y=>Math.max(0,y))),count:todo.length}

}
module.exports={discover};
