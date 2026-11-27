// Deterministic abstract invariant synthesis for
// [8,6,11,2,1,13,17,19,21,3,4,0]. Node.js, no dependencies.
// Pair alphabet 00=0,01=1,10=2,11=3. null rejects.
// T[state][input] = [next state, emitted pair string].
const T = [[[1,""],[2,""],[3,""],[4,""]],
 [[3,"1"],[4,"1"],null,null],
 [[2,"0"],[1,"0"],null,null],
 [[5,"112"],[5,"113"],null,null],
 [[3,"0"],[4,"0"],[1,"0"],[2,"0"]],
 [[5,"0"],[5,"1"],[5,"2"],[5,"3"]]];
function minimize(D) {
  let p=D.map(x=>x===null?0:1);
  for (;;) {
    let m=new Map(),q=D.map(r=>{
      let k=r===null?"bad":r.map(x=>p[x]).join(",");
      if(!m.has(k))m.set(k,m.size);return m.get(k);
    });
    let n=new Set(p).size;p=q;if(n===m.size)break;
  }
  let reps=[];for(let i=0;i<p.length;i++)reps[p[i]]=i;
  let ds=[p[0]],ix=new Map([[p[0],0]]),ret=[];
  for(let i=0;i<ds.length;i++){
    let r=D[reps[ds[i]]];if(r===null){ret.push(null);continue}
    ret.push(r.map(j=>{let v=p[j];if(!ix.has(v)){ix.set(v,ds.length);ds.push(v)}return ix.get(v)}));
  }
  return ret;
}
// K_(n+1) = K_n intersection T^-1(K_n), starting from all streams.
// Reject when the transducer fails or an emitted prefix leaves K_n.
function next(D) {
  let s=[[0,0,0]],ix=new Map([["0,0,0",0]]),res=[];
  for(let i=0;i<s.length;i++){
    let [a,b,c]=s[i];if(a<0||D[a]===null||D[c]===null){res.push(null);continue}
    res.push(Array.from({length:4},(_,x)=>{
      let t=T[b][x],v;
      if(!t)v=[-1,0,0];
      else {
        let y=c;for(let j of t[1]){if(D[y]===null)break;y=D[y][+j]}
        v=[D[a][x],t[0],y];if(D[v[0]]===null||D[y]===null)v=[-1,0,0];
      }
      let k=v.join(",");if(!ix.has(k)){ix.set(k,s.length);s.push(v)}return ix.get(k);
    }));
  }
  return minimize(res);
}
// Within a finite abstract safety monitor, seed the blank path and
// saturate the allowed edges under all input/output product paths.
function sat(D) {
  let E=D.map(()=>0),q=0;
  while(!(E[q]&1)){E[q]|=1;q=D[q][0];if(D[q]===null)throw Error("blank rejected")}
  let n=D.length;
  for(let round=0;round<1000;round++){
    let changed=false,S=[[0,0,0]],seen=new Set([0]);
    for(let i=0;i<S.length;i++){
      let [p,t,o]=S[i];
      for(let a=0;a<4;a++)if(E[p]>>a&1){
        let tr=T[t][a];if(!tr)return null;
        let j=o;
        for(let c of tr[1]){
          let b=+c,k=D[j][b];if(D[k]===null)return null;
          if(!(E[j]>>b&1)){E[j]|=1<<b;changed=true}j=k;
        }
        let v=[D[p][a],tr[0],j],key=(v[0]*6+v[1])*n+v[2];
        if(!seen.has(key)){seen.add(key);S.push(v)}
      }
    }
    if(!changed)return {E,round};
  }
  return null;
}
let D=[[0,0,0,0]];
for(let i=1;i<=30;i++){
 D=next(D);
 if(i!==30)continue;
 let s=sat(D);if(!s)throw Error("no invariant at depth 30");
 const bad=D.indexOf(null);
 let F=minimize(D.map((r,j)=>r&&s.E[j]?r.map((k,a)=>s.E[j]>>a&1?k:bad):null));
 const z=F.indexOf(null);
 let G=F.filter(x=>x!==null).map(r=>r.map(j=>j===z?null:j>z?j-1:j));
 let R=[[0,0,0]],seen=new Set(["0,0,0"]);
 for(let k=0;k<R.length;k++){
  let [a,b,c]=R[k];
  for(let x=0;x<4;x++){
   let j=G[a][x];if(j===null)continue;
   let t=T[b][x];if(!t)throw Error("bad transducer");
   let o=c;for(let y of t[1]){o=G[o][+y];if(o===null)throw Error("bad output")}
   let v=[j,t[0],o],key=v.join(",");
   if(!seen.has(key)){seen.add(key);R.push(v)}
  }
 }
 const zerosOK=G.map((_,i)=>{let j=i,s=new Set();while(j!==null&&!s.has(j)){s.add(j);j=G[j][0]}return j===null?null:i}).filter(x=>x!==null);
 const scanRel=R.filter(x=>x[1]>0&&x[1]<5).map(([a,b,c])=>[a,b-1,c]);
 console.log(JSON.stringify({depth:i,round:s.round,states:G.length,dfa:G,zerosOK,scanRel,product:R},null,2));
}
