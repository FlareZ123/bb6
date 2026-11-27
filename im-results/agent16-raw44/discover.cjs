// Exact BigInt simulation; finite translated lassos and sparse stack n-gram closure.
function discover(opt={}) {
  const base=["1RB",null,"1RC",null,"0RD",null,"1LD","1LB",null,null,null,null];
  const enc=s=>s===null||s==="---"?-1:(s.charCodeAt(2)-65)*4+(s[1]==="R"?2:0)+Number(s[0]);
  const fmt=v=>v<0?"---":`${v&1}${v&2?"R":"L"}${String.fromCharCode(65+(v>>2))}`;
  const str=p=>Array.from({length:6},(_,i)=>fmt(p[2*i])+fmt(p[2*i+1])).join("_");
  const slot=i=>String.fromCharCode(65+(i>>1))+(i&1);
  const p=base.map(enc); p[3]=enc(opt.b1||"0RC");
  const short=opt.short||120,long=opt.long||1600,maxWidth=opt.maxWidth||8,cap=opt.cap||500000;
  function run(p,T,W) {
    let q=0,l=0n,r=0n,h=0,his=[];
    for(let t=0;t<=T;t++) {
      let lo=h,hi=h;
      for(let i=his.length-1;i>=0&&i>=his.length-W;i--) {
        const s=his[i];lo=Math.min(lo,s.h);hi=Math.max(hi,s.h);
        if(s.q!==q)continue;
        const d=h-s.h;
        if(d>=0&&r===s.r&&((l^s.l)&((1n<<BigInt(s.h-lo))-1n))===0n)
          return {kind:"lasso",dir:"R",start:i,end:t,shift:d,margin:s.h-lo};
        if(d<=0&&l===s.l&&((r^s.r)&((1n<<BigInt(hi-s.h+1))-1n))===0n)
          return {kind:"lasso",dir:"L",start:i,end:t,shift:d,margin:hi-s.h};
      }
      const j=q*2+Number(r&1n),m=p[j];
      if(m<0)return {kind:"hole",t,j};
      if(t===T)return {kind:"open",t};
      his.push({q,l,r,h});
      const w=BigInt(m&1);
      if(m&2){l=(l<<1n)|w;r>>=1n;h++}
      else {r=((r>>1n)<<2n)|(w<<1n)|(l&1n);l>>=1n;h--}
      q=m>>2;
    }
  }
  function ngram(p,k,limit=200000) {
    const K=2**k,M=K-1,H=K>>1;
    const edges=[new Uint8Array(K),new Uint8Array(K)];
    const waiting=[Array.from({length:K},()=>[]),Array.from({length:K},()=>[])];
    const seen=new Set(),todo=[];
    let fail=false,over=false;
    function add(s,l,r) {
      const id=(s*K+l)*K+r;
      if(seen.has(id))return;
      seen.add(id);todo.push(id);
      if(p[s]<0)fail=true;
      if(todo.length>limit)over=true;
    }
    function pop(id,e) {
      const r=id%K,z=Math.floor(id/K),l=z%K,s=Math.floor(z/K),m=p[s],q=m>>2,w=m&1;
      if(m&2)add(2*q+(r&1),((l<<1)|w)&M,(r>>1)|(e*H));
      else add(2*q+(l&1),(l>>1)|(e*H),((r<<1)|w)&M);
    }
    function edge(d,x,e) {
      if(edges[d][x]&(1<<e))return;
      edges[d][x]|=1<<e;
      for(const id of waiting[d][x]) {pop(id,e);if(fail||over)break}
    }
    edges[0][0]=edges[1][0]=1;add(0,0,0);
    for(let i=0;i<todo.length&&!fail&&!over;i++) {
      const id=todo[i],r=id%K,z=Math.floor(id/K),l=z%K,s=Math.floor(z/K),m=p[s],w=m&1;
      const R=Boolean(m&2),push=R?l:r,popx=R?r:l,d=R?1:0;
      edge(1-d,((push<<1)|w)&M,push>>(k-1));
      if(fail||over)break;
      waiting[d][popx].push(id);
      for(let e=0;e<2;e++)if(edges[d][popx]&(1<<e))pop(id,e);
    }
    return {ok:!fail&&!over,states:todo.length,limit:over};
  }
  const first=run(p,short,64);
  if(first.kind!=="hole")return {root:str(p),first};
  const second=opt.second||"0RA";
  p[first.j]=enc(second);
  const root=str(p),rootHoles=p.filter(x=>x<0).length;
  let nodes=0,splits=0,last=0,maxQuery=0,lasso=0,ng=0,aborted=false;
  const mass={halt:0n,lasso:0n,ngram:0n,last:0n,open:0n};
  const hard=[],ngramRows=[],lateRows=[],lassoRows=[];
  const weight=h=>25n**BigInt(h);
  function visit(holes) {
    if(++nodes>cap){aborted=true;return}
    let z=run(p,short,64);
    if(z.kind==="open") {
      z=run(p,long,128);
      if(z.kind!=="open")lateRows.push({table:str(p),...z});
    }
    if(z.kind==="hole") {
      maxQuery=Math.max(maxQuery,z.t);
      if(holes===1){last++;mass.last+=25n;return}
      splits++;mass.halt+=weight(holes-1);
      for(let m=0;m<24;m++){p[z.j]=m;visit(holes-1);if(aborted)break}
      p[z.j]=-1;
    } else if(z.kind==="lasso") {
      lasso++;mass.lasso+=weight(holes);
      if(opt.dump)lassoRows.push({table:str(p),...z});
    } else {
      for(let k=1;k<=maxWidth;k++){
        const n=ngram(p,k,opt.ngramLimit||200000);
        if(n.ok){ng++;mass.ngram+=weight(holes);ngramRows.push({table:str(p),k,states:n.states});return}
        if(n.limit)break;
      }
      hard.push({table:str(p),holes});mass.open+=weight(holes);
    }
  }
  visit(rootHoles);
  const total=Object.values(mass).reduce((a,b)=>a+b,0n);
  if(!aborted&&total!==weight(rootHoles))throw Error("partition mass mismatch");
  return {root,firstHole:slot(first.j),firstQuery:first.t,rootHoles,nodes,splits,last,lasso,ngram:ng,maxQuery,weightedBound:maxQuery+6,aborted,mass:Object.fromEntries(Object.entries(mass).map(([k,v])=>[k,String(v)])),total:String(total),hard,ngramRows,lateRows,...(opt.dump?{lassoRows}:{})};
}
if(require.main===module){const opt=process.argv[2]?JSON.parse(process.argv[2]):{};console.log(JSON.stringify(discover(opt),null,2))}
module.exports=discover;
