'use strict';
// Reproducible discovery emitter: only the Lean checker certifies its result.
function generate(){
 const M=Array.from("ABCDEF").flatMap(q=>Array.from("01").flatMap(w=>Array.from("LR").map(r=>w+r+q)));
 const parse=s=>s.replaceAll("_","").match(/.../g).map(x=>x==="---"?-1:M.indexOf(x));
 const fmt=p=>Array.from({length:6},(_,i)=>p.slice(2*i,2*i+2).map(a=>a<0?"---":M[a]).join("")).join("_");
 const set=(p,s,a)=>p.map((x,i)=>i===s?a:x);
 const root=parse("1RB---_1RC---_0LA---_------_------_------");
 const order=[]; for(let w=0;w<2;w++)for(let d=0;d<2;d++)for(let q=0;q<6;q++)order.push(4*q+2*w+d);
 function classify(p,limit=1000,maxPeriod=256){
  let l=0n,r=0n,q=0,h=0;const pos=[],cfg=[],rb=new Map(),lb=new Map();
  for(let t=0;t<=limit;t++){
   cfg.push([q,l,r]);pos.push(h);const cur=Number(r&1n),s=2*q+cur,a=p[s];
   if(a<0)return ["hole",t,s];
   for(const [d,bucket,key] of [[1,rb,q+":"+r],[-1,lb,q+":"+cur+":"+l]]){
    const earlier=bucket.get(key)||[];
    for(let j=earlier.length-1;j>=0;j--){const e=earlier[j];if(t-e>maxPeriod)break;if(d*(h-pos[e])<0)continue;
     let k=0;for(let i=e;i<=t;i++)k=Math.max(k,d*(pos[e]-pos[i]));
     const [aa,bb]=d===1?[cfg[e][1],l]:[cfg[e][2]>>1n,r>>1n];
     if(((aa^bb)&((1n<<BigInt(k))-1n))===0n)return ["cycle",e,t-e,d===1,pos[e]-d*k];
    }
    earlier.push(t);bucket.set(key,earlier);
   }
   if(t===limit)break;
   const w=BigInt((a>>1)&1);q=a>>2;
   if(a&1){l=(l<<1n)|w;r>>=1n;h++;}
   else{r=((r>>1n)<<2n)|(w<<1n)|(l&1n);l>>=1n;h--;}
  }
  return ["open"];
 }
 const stats={hole:0,cycle:0,open:0,total3:0};const fresh=[],leaves=[];let maxn=0;
 function table(p){let s="(fun s => match s.1.val, s.2 with\n";for(let i=0;i<12;i++)if(p[i]>=0){const a=p[i];s+=`  | ${i>>1}, ${!!(i%2)} => some (some ⟨${M[a][0]==="1"}, ${M[a][1]==="R"}, ${a>>2}⟩)\n`;}return s+"  | _, _ => none)";}
 function gen(p){
  const c=classify(p);stats[c[0]]++;
  if(c[0]==="cycle")return `.closed (.cycle ${c[1]} ${c[2]} ${c[3]} (${c[4]}))`;
  if(c[0]==="open"){
   if(p.slice(0,6).every(a=>a>=0)){stats.total3++;const name="p"+leaves.length;leaves.push([name,table(p)]);return `.closed (.proven ${name} (closedSubsetOK_never ${name} 3 (by decide) (by decide)))`;}
   if(fmt(p)!=="1RB1LA_1RC1RB_0LA---_------_------_------")throw new Error("Unexpected open "+fmt(p));
   return ".closed (.proven BB6.Agent44Raw11A1LA.table BB6.Agent44Raw11A1LA.never)";
  }
  const [,n,s]=c;maxn=Math.max(n,maxn);
  // Preserve the original DFS numbering of the semantic leaves, then render in Lean's move order.
  const kids=[];for(let a=0;a<24;a++){const child=set(p,s,a);
   if(a>>2===3){fresh.push(fmt(child));kids.push(".unresolved");}
   else if(a>>2>3)kids.push(".unresolved");
   else kids.push(gen(child));
  }
  return `.split ${n} (${s>>1},${!!(s%2)}) (byPartialMove [\n`+order.map(a=>kids[a]).join(",\n")+"])";
 }
 // The local reference emitter numbers leaves in Lean's move order, so use that order for generation.
 function genLean(p){
  const c=classify(p);stats[c[0]]++;
  if(c[0]==="cycle")return `.closed (.cycle ${c[1]} ${c[2]} ${c[3]} (${c[4]}))`;
  if(c[0]==="open"){
   if(p.slice(0,6).every(a=>a>=0)){stats.total3++;const name="p"+leaves.length;leaves.push([name,table(p)]);return `.closed (.proven ${name} (closedSubsetOK_never ${name} 3 (by decide) (by decide)))`;}
   if(fmt(p)!=="1RB1LA_1RC1RB_0LA---_------_------_------")throw new Error("Unexpected open "+fmt(p));
   return ".closed (.proven BB6.Agent44Raw11A1LA.table BB6.Agent44Raw11A1LA.never)";
  }
  const [,n,s]=c;maxn=Math.max(n,maxn);
  return `.split ${n} (${s>>1},${!!(s%2)}) (byPartialMove [\n`+order.map(a=>{const child=set(p,s,a);if(a>>2===3){fresh.push(fmt(child));return ".unresolved";}if(a>>2>3)return ".unresolved";return genLean(child);}).join(",\n")+"])";
 }
 const body=genLean(root);
 const lean=`import Raw11ClosedSubset
import Raw11SweepA1LA

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent44Raw11
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial BB6.Agent47CanonicalFrontier
def parent : PartialMachine := ${table(root)}
`+leaves.map(([nm,t])=>`def ${nm} : PartialMachine := ${t}\n`).join("")+`
def audit : PartialAudit := ${body}

def bound : Nat := ${maxn+6}
theorem root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem nohalt : weightedTNFNoAssignedHalt parent := by
  intro s; rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide

theorem supported : TNFSupport parent 3 := supportOK_sound _ _ (by decide)
theorem checked : canonicalCheck bound parent 3 audit = true := by decide +kernel

def frontier := canonicalResiduals parent 3 audit

theorem frontier_count : frontier.length = ${fresh.length} := by decide +kernel

theorem partition (m : Machine) (hm : TNFQuotientCompatible parent m) :
    WeightedBound bound m ∨ ∃ e ∈ frontier, TNFQuotientCompatible e.2 m :=
  canonicalSound bound parent 3 audit (by decide) supported root nohalt checked m hm

/-- Consume the exact frontier at any larger common weighted bound. -/
theorem cover_from_frontier (B : Nat) (hB : bound ≤ B)
    (h : ∀ e ∈ frontier, ∀ m, TNFQuotientCompatible e.2 m → WeightedBound B m) :
    Cover (WeightedBound B) parent := by
  apply Cover.leaf
  intro m hm
  rcases partition m (compatible_quotient hm) with hb | ⟨e,he,hq⟩
  · intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) hB
  · exact h e he m hq

#print axioms cover_from_frontier
#print axioms partition
#print axioms frontier_count
end BB6.Agent44Raw11
`;
 return {lean,manifest:{root:fmt(root),bound:maxn+6,largestQuery:maxn,stats,frontier:fresh}};
}
const {lean,manifest}=generate();
const fs=require('node:fs'); const path=require('node:path');
fs.writeFileSync(path.join(__dirname,'Raw11FreshCut.lean'),lean);
fs.writeFileSync(path.join(__dirname,'fresh-frontier.json'),JSON.stringify(manifest,null,2)+'\n');
console.log({bound:manifest.bound,stats:manifest.stats,frontier:manifest.frontier.length});
