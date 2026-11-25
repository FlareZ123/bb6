function generate(){
  const parent=[7,24,11,24,14,21,3,16,12,11,24,21],order=[];
  for(let w=0;w<2;w++)for(let r=0;r<2;r++)for(let q=0;q<6;q++)order.push(4*q+2*w+r);
  const counts={cycle:0,last:0,split:0,far:0,proven:0};let maxQuery=0;
  const hard=[7,13,11,24,14,21,3,16,12,11,14,21].join(",");
  function scan(p,limit=250){
    let q=0,h=0,x=0n,off=limit+1; const hist=[];
    for(let t=0;t<=limit;t++){
      let lo=h,hi=h;
      for(let i=t-1;i>=0;i--){
        const [a,b,z]=hist[i];lo=Math.min(lo,b);hi=Math.max(hi,b);
        if(a!==q)continue;
        const d=h-b;
        if(d>=0&&(z>>BigInt(lo+off))===(x>>BigInt(lo+off+d)))return ["cycle",i,t-i,true,lo];
        if(d<=0&&(z&((1n<<BigInt(hi+off+1))-1n))===((x&((1n<<BigInt(hi+off+d+1))-1n))<<BigInt(-d)))return ["cycle",i,t-i,false,hi];
      }
      const s=2*q+Number((x>>BigInt(h+off))&1n),v=p[s];
      if(v===24)return ["hole",t,s];
      hist.push([q,h,x]); const bit=1n<<BigInt(h+off);
      x=(x&~bit)|(BigInt((v>>1)&1)<<BigInt(h+off));h+=v&1?1:-1;q=v>>2;
    }
    return ["open"];
  }
  function masks(p,rev,D){
    const d=D.length/2,N=6*d+1,h=1<<(N-1),T=Array(2*N).fill(0),rules=[];
    T[N-1]=T[2*N-1]=h;
    for(let b=0;b<2;b++)for(let l=0;l<d;l++)for(let q=0;q<6;q++){
      const a=p[2*q+b],dst=b*N+6*l+q;
      if(a===24){T[dst]=h;continue}
      const n=a>>2,w=(a>>1)&1,r=a&1;
      if(r!==rev)T[dst]=1<<(6*D[2*l+w]+n);
      else for(let j=0;j<d;j++)for(let x=0;x<2;x++)if(D[2*j+x]===l)rules.push([dst,x*N+6*j+n,w*N]);
    }
    for(let change=true;change;){
      change=false;
      for(const [dst,src,off] of rules){
        let v=T[src],nw=T[dst];
        while(v){const bit=v&-v;v-=bit;nw|=T[off+31-Math.clz32(bit)]}
        if(nw!==T[dst]){T[dst]=nw;change=true}
      }
    }
    let z=h,old;
    do{old=z;for(let i=0;i<N;i++)if(T[i]&z)z|=1<<i}while(old!==z);
    return z&1?null:`.far ${!!rev} ${d} ⟨0,[${D}],[${T.slice(0,N)}],[${T.slice(N)}],${z}⟩`;
  }
  function slot(s){return `(${s>>1},${!!(s&1)})`}
  function tree(p){
    const a=scan(p);
    if(a[0]==="cycle"){counts.cycle++;return `.cycle ${a[1]} ${a[2]} ${a[3]} (${a[4]})`}
    if(a[0]==="hole"){
      const [_,n,s]=a;maxQuery=Math.max(n,maxQuery);
      if(p.filter(v=>v===24).length===1){counts.last++;return `.last ${n} ${slot(s)}`}
      counts.split++;const children=order.map(v=>{const c=p.slice();c[s]=v;return tree(c)});
      return `.split ${n} ${slot(s)} (byMove [\n${children.join(",\n")}])`;
    }
    if(p.join(",")===hard){counts.proven++;return ".proven BB6.Agent48F1ZeroRFHard.ctr BB6.Agent48F1ZeroRFHard.never"}
    for(const D of [[0,0],[0,1,0,1]])for(const rev of [0,1]){
      const c=masks(p,rev,D);if(c){counts.far++;return c}
    }
    throw Error("unresolved "+p);
  }
  const data=tree(parent);
  if(JSON.stringify(counts)!==JSON.stringify({cycle:117,last:30,split:7,far:14,proven:1})||maxQuery!==205)throw Error(JSON.stringify({counts,maxQuery}));
  const code=`import FastThreeHoleAudit
import ChampionF1ZeroRFHard

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent48F1ZeroRF
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10FastAudit

def parent : PartialMachine := fromCodes [${parent}]
def tree : Audit := ${data}
theorem checked : fastCheck 211 parent tree = true := by decide

theorem root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt parent := by
  intro s
  unfold parent fromCodes
  cases h : ([${parent}] : List Nat)[2 * s.1.val + s.2.toNat]? with
  | none => simp [h]
  | some n =>
    by_cases hn : n < 24 <;> simp [h, hn]

noncomputable def certificate : WeightedTNFCertificate 211 parent 6 :=
  certifiedFast 211 parent tree root nohalt checked

theorem all_completions_weighted : ∀ m, compatible parent m → WeightedBound 211 m := certificate.sound

#print axioms root
#print axioms nohalt
#print axioms checked
#print axioms all_completions_weighted
end BB6.Agent48F1ZeroRF
`;
  return {code,counts,maxQuery};
}
process.stdout.write(generate().code);
