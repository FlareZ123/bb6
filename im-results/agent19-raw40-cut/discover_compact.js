/* Deterministic sparse discovery for Raw40. Usable in restricted JS runtime.
   Returns exact table strings and finite graph candidates. Not a proof checker.
   Canonical enumeration matches enumerate_canon.cpp (1000 steps, 256 cycle gap).
*/
function parse(t){return t.replaceAll("_","").match(/.../g).map(m=>m==="---"?-1:12*+m[0]+6*(m[1]==="R")+m.charCodeAt(2)-65)}
function show(p){return p.map(m=>m<0?"---":(m>=12?"1":"0")+(m%12>=6?"R":"L")+String.fromCharCode(65+m%6)).join("").match(/.{6}/g).join("_")}
function enumerate(table,options={}){
 const L=1000, O=1024,W=2048;
 const bits=Array.from({length:W},(_,i)=>1n<<BigInt(i));
 const below=bits.map(b=>2n*b-1n), mask=(1n<<BigInt(W))-1n,above=bits.map(b=>mask^(b-1n));
 const p=parse(table),opens=[],wanted=options.wanted?new Set(options.wanted):null;
 let nodes=0,done=false,openCount=0,maxScore=-1,maxWitness=null;
 function delay(p,state=0,seen=1){let best=[];for(let q=0;q<6;q++)if(!(seen>>q&1)){let a=p[2*q];if(a===-1||(a>=0&&a<12&&a%6===state)){let path=[q,...delay(p,q,seen|(1<<q))];if(path.length>best.length)best=path}}return best}
 function record(p,n,s){let q=p.slice();q[s]=-2;let path=delay(q),score=n+1+path.length;if(score>maxScore){maxScore=score;maxWitness={n,slot:s,delay:path.length,delayPath:path,table:q.map(m=>m===-2?'HHH':m<0?'---':(m>=12?'1':'0')+(m%12>=6?'R':'L')+String.fromCharCode(65+m%6)).join('').match(/.{6}/g).join('_')}}}
 function classify(p){
  let q=0,h=O,t=0n,tr=[],prev=[[],[],[],[],[],[]];
  for(let n=0;n<=L;n++){
   let s=2*q+Number((t>>BigInt(h))&1n);if(p[s]<0)return [1,n,s];
   let low=h,high=h,i=n-1,pr=prev[q];
   for(let a=pr.length-1;a>=0;a--){
    let j=pr[a];if(n-j>256)break;
    while(i>=j){let x=tr[i--][0];if(x<low)low=x;if(x>high)high=x}
    let d=h-tr[j][0];
    if(d>=0&&((tr[j][1]^(t>>BigInt(d)))&above[low])===0n)return [2];
    if(d<=0&&((tr[j][1]^(t<<BigInt(-d)))&below[high])===0n)return [2];
   }
   tr.push([h,t]);pr.push(n);
   let a=p[s];if(a>=12)t|=bits[h];else t&=~bits[h];
   h+=a%12>=6?1:-1;q=a%6;
  }return [0]
 }
 function visit(p){
  if(done)return;
  nodes++;
  let a=classify(p);
  if(a[0]===2)return;
  if(a[0]===0){
   let id=openCount++;
   if(!wanted||wanted.has(id))opens.push([id,show(p)]);
   if(wanted&&opens.length===wanted.size)done=true;
   return;
  }
  record(p,a[1],a[2]);
  if(p.filter(x=>x<0).length===1)return;
  let cut=2;for(let i=0;i<12;i++)if(p[i]>=0)cut=Math.max(cut,Math.floor(i/2)+1,p[i]%6+1);
  let s=a[2],b=p.slice();
  for(let i=0;i<24;i++)if(i%6<=cut){b[s]=i;visit(b);if(done)return}
 }
 visit(p);return {nodes,openCount,opens,stopped:done,maxScore,maxWitness};
}
function solve(table,fs,cap=30000){
 const p=parse(table),dict=fs.map(f=>new Map([[f.start,0]])),val=fs.map(f=>[f.start]),delta=[[0,0],[0,0]],incoming=[[new Set([0])],[new Set([0])]],wait=[[],[]],todo=[],seen=new Set();
 let bad=false;
 function intern(d,x){let j=dict[d].get(x);if(j===undefined){j=val[d].length;dict[d].set(x,j);val[d].push(x);incoming[d].push(new Set());delta[d].push(0,0)}return j}
 function push(d,x,b){let j=intern(d,fs[d].fn(val[d][x],b));delta[d][2*x+b]=j;return j}
 function add(s,l,r){let id=s+","+l+","+r;if(!seen.has(id)){seen.add(id);todo.push([s,l,r]);if(p[s]<0||todo.length>cap)bad=true}}
 function pop(st,e){let [s,l,r]=st,m=p[s],w=m>=12?1:0,n=m%6,b=e&1,x=e>>1;if(m%12>=6)add(2*n+b,push(0,l,w),x);else add(2*n+b,x,push(1,r,w))}
 add(0,0,0);
 for(let i=0;i<todo.length&&!bad;i++){
  let st=todo[i],[s,l,r]=st,m=p[s],w=m>=12?1:0,d=m%12>=6?0:1,x=d?r:l,y=d?l:r,z=push(d,x,w),e=2*x+w;
  if(!incoming[d][z].has(e)){incoming[d][z].add(e);for(let u of wait[d][z]||[]){pop(u,e);if(bad)break}}
  if(bad)break;
  (wait[1-d][y]||(wait[1-d][y]=[])).push(st);
  for(let e of incoming[1-d][y]){pop(st,e);if(bad)break}
 }
 let edge_counts=incoming.map(e=>e.reduce((a,b)=>a+b.size,0));
 return {ok:!bad,states:todo.length,edges:edge_counts[0]+edge_counts[1],edge_counts,dfa:delta,summary_counts:val.map(x=>x.length)}
}
function rungram([r,c0,c1,m0,m1]){
 return {start:"",fn:(s,b)=>{
  let a=s?s.split(",").map(Number):[];
  if(!a.length&&!b)return "";
  if(a[0]===b){let c=b?c1:c0,m=b?m1:m0;a[1]++;if(a[1]>=c+m)a[1]=c;return a.join(",")}
  return [b,1,...a].slice(0,2*r).join(",")
 }}
}
function ngram(k){let mask=(1<<k)-1;return {start:0,fn:(x,b)=>((x<<1)|b)&mask}}
function laggram([k,r,c0,c1,m0,m1]){
 let g=rungram([r,c0,c1,m0,m1]),mask=(1<<k)-1;
 return {start:"0|",fn:(s,b)=>{let [x,y]=s.split("|");x=+x;return (((x<<1)|b)&mask)+"|"+g.fn(y,k?b^(x>>(k-1)):b)}}
}
function findLag(table,params,cap=30000){
 let [k,r,m0,m1]=params;
 for(let k1 of new Set([k,k+1,k+2,3,4,5,6,7,8]))for(let r1 of new Set([r+1,r,r+2,1,2,3,4]))for(let [c0,c1] of [[1,2],[1,1],[2,2],[2,1],[1,3],[3,3],[3,1]])for(let [a,b] of [[m0,m1],[m0,4],[m0,2],[m0,3],[2*m0,m1],[m0,2*m1]]){
  let p=[k1,r1,c0,c1,a,b],g=laggram(p),s=solve(table,[g,g],cap);
  if(s.ok)return {...s,method:["compact-lag",p,p]}
 }return {ok:false};
}
