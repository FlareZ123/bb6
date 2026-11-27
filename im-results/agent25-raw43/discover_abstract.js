// Untrusted finite-state abstraction discovery. The returned DFA pair is checked independently
// by agent32-raw59/emit_rungram.py and FastBiDFA. A failed search proves nothing.
function parse(s){return s.replaceAll("_","").match(/.../g).map(v=>v==="---"?-1:12*(+v[0])+6*(v[1]==="R")+(v.charCodeAt(2)-65))}
function dfa(params){
 const [k,c0,c1,m0,m1]=params,words=[[]],ids=new Map([["",0]]),delta=[[-1,-1]];
 function push(i,b){if(delta[i][b]>=0)return delta[i][b];const v=words[i];let w;
 if(!v.length)w=b?[1,1]:[];
 else if(v[0]===b){const c=b?c1:c0,m=b?m1:m0;let n=v[1]+1;if(n===c+m)n=c;w=[b,n,...v.slice(2)]}
 else w=[b,1,...v].slice(0,2*k);
 let key=w.join(","),j=ids.get(key);if(j===undefined){j=words.length;ids.set(key,j);words.push(w);delta.push([-1,-1])}delta[i][b]=j;return j}
 return {push,finish:()=>delta.flat().map(x=>Math.max(0,x)),size:()=>words.length}
}
function winDfa(k){const M=2**k,ids=new Map([[0,0]]),words=[0],delta=[[-1,-1]];return {push:(x,b)=>{if(delta[x][b]>=0)return delta[x][b];let w=(words[x]*2+b)%M,j=ids.get(w);if(j===undefined){j=words.length;ids.set(w,j);words.push(w);delta.push([-1,-1])}delta[x][b]=j;return j},finish:()=>delta.flat().map(x=>Math.max(0,x)),size:()=>words.length}}

function blockDfa(params){
const {k,periods,c,m}=params,words=[""],ids=new Map([["",0]]),delta=[[-1,-1]];
function norm(w){let changed=true;while(changed){changed=false;outer:for(let i=0;i<w.length;i++)for(const p of periods){const end=i+p*(c+m);if(end>w.length)continue;let a=w.slice(i,i+p);if(a.repeat(c+m)===w.slice(i,end)){w=w.slice(0,i)+w.slice(i+m*p);changed=true;break outer;}}}return w.slice(0,k).replace(/0+$/,"")}
return {push:(x,b)=>{if(delta[x][b]>=0)return delta[x][b];let w=norm(b+words[x]),j=ids.get(w);if(j===undefined){j=words.length;ids.set(w,j);words.push(w);delta.push([-1,-1])}delta[x][b]=j;return j},finish:()=>delta.flat().map(x=>Math.max(0,x)),size:()=>words.length}}

function solve(table,left,right,cap=30000){
 const tr=typeof table==="string"?parse(table):table,d=[typeof left==="number"?winDfa(left):Array.isArray(left)?dfa(left):blockDfa(left),typeof right==="number"?winDfa(right):Array.isArray(right)?dfa(right):blockDfa(right)],edges=[new Map(),new Map()],waiting=[new Map(),new Map()],seen=new Set(),todo=[],H=2**24,Q=H*H;let fail=false,limit=false;
 function add(s,l,r){const x=s*Q+l*H+r;if(seen.has(x))return;seen.add(x);todo.push([s,l,r]);if(tr[s]<0)fail=true;if(todo.length>cap||l>=H||r>=H)limit=true}
 function pop(st,e){const [s,l,r]=st,m=tr[s],w=m/12|0,q=m%6,dir=m%12>=6,b=e[0],src=e[1];if(dir)add(2*q+b,d[0].push(l,w),src);else add(2*q+b,src,d[1].push(r,w))}
 function list(m,i){let v=m.get(i);if(!v){v=[];m.set(i,v)}return v}
 for(const e of edges)e.set(0,[[0,0]]);
 add(0,0,0);
 for(let i=0;i<todo.length&&!fail&&!limit;i++){let st=todo[i];const [s,l,r]=st,m=tr[s],w=m/12|0,side=+(m%12>=6),other=1-side,old=side?l:r,dest=d[other].push(old,w),x=side?r:l,es=list(edges[other],dest);
 if(!es.some(e=>e[0]===w&&e[1]===old)){const e=[w,old];es.push(e);for(const st2 of list(waiting[other],dest)){pop(st2,e);if(fail||limit)break}}
 if(fail||limit)break;list(waiting[side],x).push(st);for(const e of list(edges[side],x)){pop(st,e);if(fail||limit)break}
 }
 return fail||limit?{status:fail?"fail":"cap",states:todo.length}:{status:"ok",dfa:d.map(x=>x.finish()),states:todo.length,edges:edges.reduce((n,x)=>n+[...x.values()].reduce((a,v)=>a+v.length,0),0),params:[left,right]}
}
const presets=[];
for(let k=1;k<=9;k++)presets.push(k);
for(let k=1;k<=4;k++)for(const c of [1,2,3,4])for(const m of [1,2,3,4])presets.push([k,c,c,m,m]);
function search(t,cap=10000,more=[]){let best={status:"fail",states:0};for(const p of [...more,...presets]){let z=solve(t,p,p,cap);if(z.status==="ok")return z;if(z.states>best.states)best={...z,params:[p,p]}}return best}
return {parse,dfa,solve,search,presets};
