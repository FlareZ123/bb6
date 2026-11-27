// Automatically discover finite symbolic return maps and closed regular languages.
// Input: node synth_sweep_transducer.js '[8,6,11,2,1,13,17,19,21,3,4,0]'
// Outputs untrusted certificate JSON, with exact macro identities on arbitrary tails.
// A Lean source bridge is still needed for original-machine acceptance.
function primitive(M,c) {
  let [q,l,r]=c;if(!r.length)return null;
  let v=M[2*q+ +r[0]]-1;if(v<0)return null;
  let w=String((v>>1)&1);
  if(v&1)return [v>>2,w+l,r.slice(1)];
  if(!l.length)return null;
  return [v>>2,l.slice(1),l[0]+w+r.slice(1)];
}
function blocks(s,k) {
  if(s.length%k)return null;
  let a=[];for(let i=0;i<s.length;i+=k)a.push(parseInt(s.slice(i,i+k),2));return a;
}
function synth(M,q,k,m) {
  let N=1<<k,bin=a=>a.toString(2).padStart(k,"0"),marker="0".repeat(m),transfer=[],transferCost=[];
  // Left and right strings terminate in distinct arbitrary, untouched tails.
  for(let a=0;a<N;a++){
    let c=[q,"",bin(a)];
    for(let t=1;t<=64;t++){
      c=primitive(M,c);if(!c)break;
      if(c[0]===q&&!c[2].length){
        let a2=blocks(c[1],k);if(a2){transfer[a]=a2;transferCost[a]=t}break;
      }
    }
  }
  if(!transfer.some(x=>x!==undefined))return null;
  function output(r){
    let b=blocks(r,k);if(!b||b.some(x=>transfer[x]===undefined))return null;
    return b.reverse().flatMap(x=>transfer[x]);
  }
  let T=[Array.from({length:N},(_,a)=>[a+1,[]])],mac=[];
  for(let p=0;p<N;p++){
    T[p+1]=[];mac[p]=[];
    for(let a=0;a<N;a++){
      let c=[q,bin(p)+bin(a),marker],found=null;
      for(let t=1;t<=100;t++){
        c=primitive(M,c);if(!c)break;if(c[0]!==q)continue;
        let [_,l,r]=c;
        if(l.length===k&&r.startsWith(marker)){
          let o=output(r.slice(m));
          if(o!==null){found=[parseInt(l,2)+1,o];mac[p][a]={t,l,r,mode:"scan"};break}
        }
        let o=output(r),tail=blocks(l,k);
        if(o!==null&&tail!==null){found=[N+1,o.concat(tail)];mac[p][a]={t,l,r,mode:"turn"};break}
      }
      T[p+1][a]=found;
    }
  }
  T[N+1]=Array.from({length:N},(_,a)=>[N+1,[a]]);
  return {T,mac,transfer,transferCost,q,k,m};
}
function minimize(D){
  let p=D.map(x=>x===null?0:1);
  for(;;){
    let m=new Map(),r=D.map(x=>{
      let k=x===null?"bad":x.map(j=>p[j]).join(",");
      if(!m.has(k))m.set(k,m.size);return m.get(k);
    });
    let n=new Set(p).size;p=r;if(n===m.size)break;
  }
  let reps=[];for(let i=0;i<p.length;i++)reps[p[i]]=i;
  let ds=[p[0]],ix=new Map([[p[0],0]]),ret=[];
  for(let i=0;i<ds.length;i++){
    let r=D[reps[ds[i]]];if(r===null){ret.push(null);continue}
    ret.push(r.map(j=>{let v=p[j];if(!ix.has(v)){ix.set(v,ds.length);ds.push(v)}return ix.get(v)}));
  }
  return ret;
}
function next(D,T,N,cap=100000) {
  let s=[[0,0,0]],ix=new Map([["0,0,0",0]]),res=[];
  for(let i=0;i<s.length;i++){
    if(s.length>cap)return null;
    let [a,b,c]=s[i];if(a<0||D[a]===null||D[c]===null){res.push(null);continue}
    res.push(Array.from({length:N},(_,x)=>{
      let t=T[b][x],v;
      if(!t)v=[-1,0,0];
      else{
        let y=c;for(let j of t[1]){if(D[y]===null)break;y=D[y][j]}
        v=[D[a][x],t[0],y];if(D[v[0]]===null||D[y]===null)v=[-1,0,0];
      }
      let k=v.join(",");if(!ix.has(k)){ix.set(k,s.length);s.push(v)}return ix.get(k);
    }));
  }
  return minimize(res);
}
function sat(D,T,N,word){
  let E=D.map(()=>0),q=0,n=D.length;
  for(let a of word){if(D[q]===null)return null;E[q]|=1<<a;q=D[q][a]}
  while(D[q]!==null&&!(E[q]&1)){E[q]|=1;q=D[q][0]}
  if(D[q]===null)return null;
  for(let round=0;round<1000;round++){
    let changed=false,S=[[0,0,0]],seen=new Set([0]);
    for(let i=0;i<S.length;i++){
      let [p,t,o]=S[i];
      for(let a=0;a<N;a++)if(E[p]>>a&1){
        let tr=T[t][a];if(!tr)return null;
        let j=o;
        for(let b of tr[1]){
          let k=D[j][b];if(D[k]===null)return null;
          if(!(E[j]>>b&1)){E[j]|=1<<b;changed=true}j=k;
        }
        let v=[D[p][a],tr[0],j],key=(v[0]*T.length+v[1])*n+v[2];
        if(!seen.has(key)){seen.add(key);S.push(v)}
      }
    }
    if(!changed)return {E,round};
  }
  return null;
}
function certificate(D,s,T,N){
  const bad=D.indexOf(null),reject=bad<0?D.length:bad;
  let H=D.map((r,j)=>r&&s.E[j]?r.map((k,a)=>s.E[j]>>a&1?k:reject):null);
  if(bad<0)H.push(null);
  let F=minimize(H),z=F.indexOf(null);
  let G=F.filter(x=>x!==null).map(r=>r.map(j=>j===z?null:z>=0&&j>z?j-1:j));
  let R=[[0,0,0]],seen=new Set(["0,0,0"]);
  for(let k=0;k<R.length;k++){
    let [a,b,c]=R[k];for(let x=0;x<N;x++){
      let j=G[a][x];if(j===null)continue;
      let t=T[b][x];if(!t)throw Error("bad transducer");
      let o=c;for(let y of t[1]){o=G[o][y];if(o===null)throw Error("bad output")}
      let v=[j,t[0],o],key=v.join(",");
      if(!seen.has(key)){seen.add(key);R.push(v)}
    }
  }
  const zerosOK=G.map((_,i)=>{
    let j=i,s=new Set();while(j!==null&&!s.has(j)){s.add(j);j=G[j][0]}return j===null?null:i
  }).filter(x=>x!==null);
  return {dfa:G,zerosOK,product:R,round:s.round};
}
function invariant(spec,word,maxDepth=64){
  let {T,k}=spec,N=1<<k,D=[Array(N).fill(0)];
  for(let i=1;i<=maxDepth;i++){
    D=next(D,T,N);if(!D||D.length>5000)return null;
    let s=sat(D,T,N,word);
    if(s)return {depth:i,...certificate(D,s,T,N)};
  }
  return null;
}
function rootSeeds(M,limit=1024){
  let q=0,l=0n,r=0n,seeds=new Map();
  for(let t=0;t<=limit;t++){
    if(r===0n&&!seeds.has(q))seeds.set(q,{t,bits:l===0n?"":l.toString(2).split("").reverse().join("")});
    let v=M[2*q+Number(r&1n)]-1;if(v<0)break;
    let w=BigInt((v>>1)&1);
    if(v&1){l=(l<<1n)|w;r>>=1n}else{r=((r>>1n)<<2n)|(w<<1n)|(l&1n);l>>=1n}q=v>>2;
  }
  return seeds;
}
// Cheap screen: reject return maps that fail on actual finite-word orbit.
// A repeated (buffer,input-end) in a nonturn scan is safe, but the
// full regular-language checker remains the acceptance gate.
function screen(T,N,word,rounds=80){
  let w=word;
  for(let i=0;i<rounds;i++){
    let q=0,o=[],done=false,seen=new Set();
    for(let j=0;j<=w.length+T.length+1;j++){
      if(j>=w.length){if(seen.has(q))return true;seen.add(q)}
      let t=T[q][w[j]??0];if(!t)return false;
      q=t[0];o.push(...t[1]);
      if(q===N+1){o.push(...w.slice(j+1));done=true;break}
    }
    if(!done)return false;
    while(o.length&&o[o.length-1]===0)o.pop();
    w=o;if(w.length>20000)return true;
  }
  return true;
}
function search(M,maxDepth=64){
  for(let [q,seed] of rootSeeds(M)){
    for(let k=1;k<=3;k++){
      let N=1<<k,w=blocks(seed.bits.padEnd(Math.ceil(seed.bits.length/k)*k,"0"),k);
      for(let m=1;m<=4;m++){
        let spec=synth(M,q,k,m);if(!spec||!screen(spec.T,N,w))continue;
        let cert=invariant(spec,w,maxDepth);
        if(cert)return {M,seed,word:w,...spec,...cert};
      }
    }
  }
  return null;
}
if(typeof module!=="undefined")module.exports={primitive,blocks,synth,minimize,next,sat,certificate,invariant,rootSeeds,screen,search};
if(typeof require!=="undefined"&&require.main===module){
  let M=JSON.parse(process.argv[2]),res=search(M,Number(process.argv[3]??64));
  console.log(JSON.stringify(res,null,2));
  if(!res)process.exitCode=1;
}
