
const rows5=[[3,2,-1,3,-1],[18,2,19,3,-1],[18,2,23,3,-1],[19,2,-1,3,2],[19,2,-1,3,3],[19,2,-1,3,18],[19,2,-1,3,19],[21,2,-1,3,-1],[22,2,-1,3,19],[4,3,19,3,-1],[4,4,19,3,-1],[5,4,19,3,-1],[8,4,19,3,-1],[3,18,2,3,-1],[3,18,3,3,-1],[3,18,18,3,-1],[23,18,6,3,-1],[23,18,8,3,-1],[23,18,18,3,-1],[-1,19,20,3,23],[21,20,-1,3,2],[-1,20,8,3,23],[-1,20,18,3,23],[-1,20,20,3,23],[3,23,-1,3,24],[6,23,-1,3,24],[3,24,-1,3,2],[3,24,-1,3,8],[3,24,-1,3,24],[4,24,19,3,-1],[3,2,-1,20,3],[19,2,-1,20,3],[21,2,-1,20,3],[24,-1,1,20,23],[2,-1,2,20,23],[18,-1,2,20,23],[20,-1,2,20,23],[23,-1,2,20,23],[-1,24,5,20,23],[-1,-1,18,20,23],[-1,-1,20,20,23]];
const rows=rows5.map(([a,b,e,f,g])=>[8,a,11,b,13,13,14,17,21,e,f,g]);
const lit=w=>w?[[w,false]]:[],rep=w=>[[w,true]];
function clean(w){let out=[];for(const [a,b] of w){if(!a)continue;if(!b&&out.length&&!out.at(-1)[1])out.at(-1)[0]+=a;else out.push([a,b])}return out}
const prefix=w=>w.length&&!w[0][1]?w[0][0]:"",rest=w=>prefix(w)?w.slice(1):w;
function head(w){if(!w.length)return "0";if(w[0][1])throw 0;return w[0][0][0]}
function tail(w){if(!w.length)return [];if(w[0][1])throw 0;return clean([...lit(w[0][0].slice(1)),...w.slice(1)])}
const cons=(a,w)=>clean([...lit(a),...w]);
function norm(w){w=clean(w);while(true){let changed=false;for(let i=1;i<w.length;i++){let [p,pr]=w[i-1],[b,br]=w[i];if(!pr&&br&&p.at(-1)===b.at(-1)){let z=p.at(-1);w=clean([...w.slice(0,i-1),...lit(p.slice(0,-1)),...rep(z+b.slice(0,-1)),...lit(z),...w.slice(i+1)]);changed=true;break}}if(!changed)return w}}
const key=c=>JSON.stringify([c[0],norm(c[1]),norm(c[2])]);
function step(row,c){let [q,l,r]=c,a=row[2*q+Number(head(l))];if(a<=0)throw 0;let n=a-1,w=String((n>>1)&1),s=n>>2;return n&1?[s,cons(head(r),cons(w,tail(l))),tail(r)]:[s,tail(l),cons(w,r)]}
const eq=(a,b)=>JSON.stringify(a)===JSON.stringify(b);
function local(row,q,lp,rp,side,I){let c=[q,clean([...lit(lp+(side==="L"?I:"")),...rep("X")]),clean([...lit(rp+(side==="R"?I:"")),...rep("Y")])];for(let k=1;k<=100;k++){try{c=step(row,c)}catch{return null}if(c[0]!==q)continue;let l=prefix(c[1]),r=prefix(c[2]);if(!eq(rest(c[1]),rep("X"))||!eq(rest(c[2]),rep("Y")))continue;if(side==="L"&&l===lp&&r.startsWith(rp)&&r.length===rp.length+I.length)return [k,r.slice(rp.length)];if(side==="R"&&r===rp&&l.startsWith(lp)&&l.length===lp.length+I.length)return [k,l.slice(lp.length)]}return null}
function moves(row,c){let out=[];for(const side of ["L","R"]){let [q,l,r]=c,[w,o]=side==="L"?[l,r]:[r,l];let lp=prefix(w),wr=rest(w),op=prefix(o);if(!wr.length)continue;let I=wr[0][0];for(let j=0;j<=Math.min(20,op.length);j++){let a=local(row,q,side==="L"?lp:op.slice(0,j),side==="L"?op.slice(0,j):lp,side,I);if(!a)continue;let [k,O]=a,w2=clean([...lit(lp),...wr.slice(1)]),o2=clean([...lit(op.slice(0,j)),...rep(O),...lit(op.slice(j)),...rest(o)]);out.push([side==="L"?[q,w2,o2]:[q,o2,w2],k,true])}}try{out.push([step(row,c),1,false])}catch{}return out}
function pump(row,st,tg,bfs=false){let tk=key(tg),seen=new Set([key(st)]),todo=[[st,0,0,0]];for(let i=0;i<todo.length&&seen.size<1500;i++){let [c,a,b,d]=todo[i];if(key(c)===tk)return [a,b,d];if(d>=200)continue;let ms=moves(row,c);if(!bfs)ms=ms.slice(0,1);for(let [s,k,r] of ms){let sk=key(s);if(seen.has(sk))continue;seen.add(sk);todo.push([s,a+(r?0:k),b+(r?k:0),d+1])}}return null}
function inserts(a,b,c){let d=b.length-a.length;if(d<0||d>24||c.length!==b.length+d)return [];if(!d)return a===b&&b===c?[[lit(a),lit(a)]]:[];let out=[],seen=new Set;for(let k=0;k<=a.length;k++){let I=b.slice(k,k+d);if(b!==a.slice(0,k)+I+a.slice(k)||c!==a.slice(0,k)+I+I+a.slice(k))continue;let st=clean([...lit(a.slice(0,k)),...rep(I),...lit(a.slice(k))]),tg=clean([...lit(a.slice(0,k)+I),...rep(I),...lit(a.slice(k))]);let key=JSON.stringify(norm(st));if(seen.has(key))continue;seen.add(key);out.push([st,tg])}return out}
function find(row){let c=[0,[],[]],groups=new Map,all=[];for(let t=0;t<4000;t++){let [q,l,r]=c,ls=prefix(l),rs=prefix(r),h=head(l),tags=[];if(q===3&&h==="1")tags.push("D1");if(!l.length||!r.length)tags.push("edge:"+q+":"+h+":"+(!l.length?"L":"R"));tags.push("all:"+q+":"+h);for(let tag of tags){if(!groups.has(tag))groups.set(tag,[]);let g=groups.get(tag);if(g.length<180)g.push([t,q,ls,rs])}try{c=step(row,c)}catch{break}}
let candidates=[],seen=new Set;for(let [tag,g] of groups){for(let i=0;i<Math.min(40,g.length);i++)for(let p=1;p<=Math.min(tag.startsWith("all")?8:12,Math.floor((g.length-1-i)/2));p++){let [t,q,l,r]=g[i],b=g[i+p],c=g[i+2*p];let L=inserts(l,b[2],c[2]),R=inserts(r,b[3],c[3]);if(!L.length||!R.length)continue;for(let [ls,lt] of L)for(let [rs,rt] of R){if(!ls.some(x=>x[1])&&!rs.some(x=>x[1]))continue;let st=[q,ls,rs],tg=[q,lt,rt],k=key(st)+"|"+key(tg);if(seen.has(k))continue;seen.add(k);candidates.push({t,st,tg,tag})}}}
candidates.sort((a,b)=>Number(b.tag==="D1")-Number(a.tag==="D1")||a.t-b.t);
for(let i=0;i<Math.min(candidates.length,160);i++){let s=candidates[i],p=pump(row,s.st,s.tg);if(p)return {...s,proof:p}}
for(let i=0;i<Math.min(candidates.length,30);i++){let s=candidates[i],p=pump(row,s.st,s.tg,true);if(p)return {...s,proof:p,bfs:true}}
return {failure:true,candidates:candidates.length}
}
function discover(){return rows.map((row,i)=>({i,row,...find(row)}))}

console.log(JSON.stringify(discover(),null,2))
