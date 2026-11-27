// Exact finite entry, with no F1 row. Regenerate Lean RLE certificates.
const fs=require("fs"),path=require("path");
function exits(f){
 const t=[7,23,11,12,15,1,6,18,4,17,f,24],e={};
 for(let q=0;q<6;q++)for(let d=0;d<2;d++)for(let a=0;a<8;a++){
  let p=d?0:2,b=a,r=q,k=0;
  while(p>=0&&p<3&&k<145){let c=t[2*r+((b>>p)&1)];if(c===24)break;
   b=(b&~(1<<p))|(((c>>1)&1)<<p);r=c>>2;p+=(c&1)?1:-1;k++}
  if(p<0||p>=3)e[[q,d,a]]=[r,p>=3?1:0,b,k];
 }return e;
}
const fmtStack=S=>"["+S.map(([a,n])=>"(S "+a+","+n+")").join(",")+"]";
function build(f,target,m,n,s,expectedK){
 let E=exits(f),q=2,d=1,L=[[6,1]],R=[],t=2,k=0,M="M"+f,j=0,lines=["namespace X"+f,"def s0 : RState := ⟨2,true,[(S 6,1)],[]⟩"],cost=0,le=0,edges=[];
 const fmt=()=>"⟨"+q+","+(d?"true":"false")+","+fmtStack(L)+","+fmtStack(R)+"⟩";
 function push(S,a,n){if(!S.length&&a===0)return;if(S.length&&S[0][0]===a)S[0][1]+=n;else S.unshift([a,n])}
 while(t<target){let S=d?R:L,[a,n]=S[0]||[0,1],z=E[[q,d,a]];if(!z)throw Error("undefined");if(q!==z[0]||d!==z[1])n=1;if(S.length){S[0][1]-=n;if(S[0][1]===0)S.shift()}[q,d,a]=z;push(d?L:R,a,n);t+=n*z[3];cost+=n*z[3];k++;le++;
 if(le===512||t===target){j++;lines.push("def s"+j+" : RState := "+fmt(),"theorem e"+j+" : Raw140Sweep.execute "+M+" "+le+" s"+(j-1)+" = some ("+cost+",s"+j+") := by decide +kernel");edges.push([j,le,cost]);cost=0;le=0}}
 const expand=S=>S.map(([a,n])=>String(a).repeat(n)).join("");
 if(t!==target||k!==expectedK||q!==1||d!==1||expand(L)!=="5".repeat(m)||expand(R)!=="644".repeat(n)+s)throw Error("entry mismatch");
 lines.push("theorem entry : run "+M+" "+target+" primBlank = some (orbitCfg "+m+" "+n+" .s"+s+") := by",
 "  have h0 : run "+M+" 2 primBlank = some s0.prim := run_ext "+M+" (fill_extends _ _) _ _ _ base_start");
 for(let [j,le,cost] of edges)lines.push("  have h"+j+" := join h"+(j-1)+" (Raw140Sweep.execute_sound "+M+" "+le+" "+cost+" s"+(j-1)+" s"+j+" e"+j+")");
 lines.push("  exact h"+j,
 "theorem good : Good (orbitCfg "+m+" "+n+" .s"+s+") := ⟨"+m/2+","+(n-2)+",_,by decide,rfl⟩",
 "theorem forever (k : Nat) : ∃ c, run "+M+" k primBlank = some c := foreverEntry "+M+" progress"+f+" "+target+" _ good entry k",
 "#print axioms forever","end X"+f);
 return lines.join("\n")+"\n";
}
const output="import Raw140DoubleClosure\nimport Raw140Sweep\nnamespace Raw140Double\nopen BB6BlockFAR Raw140Orbit Raw140Extra Raw140Sweep\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"+build(4,42133,78,5,"62",8766)+build(13,44429,80,5,"6221",9015)+"end Raw140Double\n";
fs.writeFileSync(path.join(__dirname,"Raw140DoubleEntry.lean"),output);
