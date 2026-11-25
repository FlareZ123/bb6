// Deterministic raw139 candidate witness generator.
import { writeFileSync } from "node:fs";
function generate(){
const moves=[];for(const w of "01")for(const d of "LR")for(const q of "ABCDEF")moves.push(w+d+q);
const full="1RB0LE_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LD---".replaceAll("_","").match(/.../g).map(x=>x==="---"?null:x);
const parent=full.map((x,i)=>[0,2,4,7,9].includes(i)?x:null);
const schedule=[10,6,3,5,8];
const refine=(p,s,m)=>p.map((x,i)=>i===s?m:x);
const code=p=>Array.from({length:6},(_,i)=>(p[2*i]||"---")+(p[2*i+1]||"---")).join("_");
function simulate(p,cap,period=100){
 let q=0,h=0,ones=new Set(),hist=[],seen=Array.from({length:6},()=>[]);
 for(let n=0;n<=cap;n++){
  for(let j=seen[q].length-1;j>=0;j--){
   let i=seen[q][j];if(n-i>period)break;
   let old=hist[i],delta=h-old.h,lo=Infinity,hi=-Infinity;
   for(let k=i;k<n;k++){lo=Math.min(lo,hist[k].h);hi=Math.max(hi,hist[k].h)}
   for(const right of [true,false]){
    if(right?delta<0:delta>0)continue;
    let b=right?lo:hi,side=(x,b)=>right?x>=b:x<=b;
    let same=true;
    for(const x of old.ones)if(side(x,b)&&!ones.has(x+delta)){same=false;break}
    if(same)for(const x of ones)if(side(x,b+delta)&&!old.ones.has(x-delta)){same=false;break}
    if(same)return ["cycle",i,n-i,right,b]
   }
  }
  const s=2*q+Number(ones.has(h)),m=p[s];
  if(!m)return ["hole",n,s];
  if(n===cap)return ["timeout",n];
  seen[q].push(n);hist.push({h,ones:new Set(ones)});
  if(m[0]==="1")ones.add(h);else ones.delete(h);
  h+=m[1]==="R"?1:-1;q=m.charCodeAt(2)-65;
 }
}
function far(p,dfa,rev){
 const d=dfa.length/2,N=6*d+1,H=N-1,halt=1n<<BigInt(H),T=Array(2*N).fill(0n),rules=[];
 T[H]=T[N+H]=halt;
 const bit=i=>1n<<BigInt(i);
 for(let l=0;l<d;l++)for(let q=0;q<6;q++)for(let a=0;a<2;a++){
  const m=p[2*q+a],i=a*N+6*l+q;
  if(!m){T[i]=halt;continue}
  const w=Number(m[0]),next=m.charCodeAt(2)-65;
  if((m[1]==="R")!==rev)T[i]=bit(6*dfa[2*l+w]+next);
  else for(let j=0;j<d;j++)for(let b=0;b<2;b++)if(dfa[2*j+b]===l)rules.push([i,b*N+6*j+next,w*N]);
 }
 function compose(x,off){let r=0n;for(let i=0;i<N;i++)if(x&bit(i))r|=T[off+i];return r}
 for(;;){
  let changed=false;
  for(const [dst,src,off] of rules){let v=T[dst]|compose(T[src],off);if(v!==T[dst]){T[dst]=v;changed=true}}
  if(!changed)break;
 }
 let z=halt;
 for(;;){let next=z;for(let i=0;i<N;i++)if(T[i]&z)next|=bit(i);if(z===next)break;z=next}
 if(z&1n)return null;
 return ["far",rev,d,dfa,T.slice(0,N).map(String),T.slice(N).map(String),String(z)];
}
const dfas=[[0,1,0,1],[0,1,0,2,0,2],[0,5,2,6,3,3,3,2,2,4,1,7,0,5,2,1]];
const counts={},residuals=[],records=[];
let largestHalt=0;
function leaf(p,addr,obs,region){
 let v=obs;
 // Two linear-drift cases require a period window beyond the initial 100.
 if(obs[0]==="timeout" && ["1RB1LC_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LD---","1RB0LC_1RC0RC_1LD0RB_1LA0LE_1RD1LF_1LD---"].includes(code(p))) {
   const longer=simulate(p,500,200);
   if(longer[0]!=="cycle")throw Error("expected long side cycle");
   v=obs=longer;
 }
 if(obs[0]==="hole"&&p.filter(x=>x===null).length===1){v=["last",obs[1],obs[2]];largestHalt=Math.max(largestHalt,obs[1])}
 else if(obs[0]==="timeout"&&p.filter(x=>x===null).length===1){
  for(const dfa of dfas){const r=far(p,dfa,true);if(r){v=r;break}}
 }
 if(!["cycle","last","far"].includes(v[0])){v=["open"];residuals.push({address:addr,table:code(p),holes:p.filter(x=>x===null).length,observation:obs})}
 const key=region+":"+v[0];counts[key]=(counts[key]||0)+1;
 records.push({address:addr,table:code(p),witness:v});
 return v;
}
function rec(p,idx,addr){
 const s=schedule[idx],o=simulate(p,400);
 if(o[0]!=="hole"||o[2]!==s)throw Error("bad path "+code(p)+" "+o);
 const kids=moves.map(m=>{
  let t=refine(p,s,m),a=[...addr,m];
  if(idx<schedule.length-1){
   if(m===full[s])return rec(t,idx+1,a);
   return leaf(t,a,simulate(t,250),"prefix");
  }
  const v=simulate(t,400);
  if(v[0]==="hole"&&t.filter(x=>x===null).length===2){
   return ["split",v[1],v[2],moves.map(x=>{let u=refine(t,v[2],x);return leaf(u,[...a,x],simulate(u,500),"e0")})];
  }
  return leaf(t,a,v,"e0");
 });
 return ["split",o[1],s,kids];
}
const tree=rec(parent,0,[]);
const mass=residuals.reduce((s,r)=>s+25n**BigInt(r.holes),0n);
return {tree,counts,residuals,records,largestHalt,remainingMass:String(mass),parent:code(parent),totalMass:String(25n**7n)};
}
const result=generate();
writeFileSync(process.argv[2]||"witness-data.json",JSON.stringify(result,null,2)+"\n");
console.log(result.counts,result.residuals.length,result.largestHalt,result.remainingMass);
