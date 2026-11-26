// Deterministic candidate generation; Lean canonicalCheck is the proof gate.
"use strict";
const fs=require("node:fs");
const path=require("node:path");
function generate(){
 const tables=["1RB0LE_1RC0LB_1RD0RC_1LA1RC_HHH1LF_1LB1LD","1RB0LE_1RCHHH_1RD1RE_1LA0RF_0RC0LA_0LC0RB","1RB0RA_1RC0RD_1RD0LC_1LE1RA_HHH1LF_1RB0LC","1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RDHHH","1RB1LF_1RC1RB_1RD0RB_0LE0LF_HHH1LD_0LE1LA","1RB0LC_1RC0RA_1RD0RF_0LEHHH_1LB1LA_1LD1RA","1RB1LA_1RC0LE_1RD0LF_0LA0RD_1LC0LE_HHH0RE"];
 const parse=s=>s.replaceAll("_","").match(/.../g).map(x=>x==="HHH"||x==="---"?-1:12*Number(x[0])+6*Number(x[1]==="R")+x.charCodeAt(2)-65);
 const targets=tables.map(parse), parent=parse("1RB---_1RC---_1RD---_------_------_------");
 const stats={split:0,cycle:0,last:0,open:0,alias:0,maxQuery:0,maxCycleEnd:0,hits:[]}, residuals=[];
 const same=(a,b)=>a.every((x,i)=>x===b[i]);
 const extendsP=(p,t)=>p.every((x,i)=>x===-1||x===t[i]);
 const slot=s=>`(${Math.floor(s/2)},${s%2?"true":"false"})`;
 const classify=(p,targetPath)=>{
  let q=0,h=0,t=new Set(),hist=[];
  for(let n=0;n<=(targetPath?6100:128);n++){
   let s=2*q+Number(t.has(h)),m=p[s];
   if(m===-1)return {kind:"hole",n,s};
   if(!targetPath){
   for(let j=hist.length-1;j>=0;j--){
    let a=hist[j];if(a.q!==q)continue;
    let d=h-a.h;
    for(const right of (d===0?[false,true]:[d>0])){
     let b=h;for(let k=j;k<n;k++)b=right?Math.min(b,hist[k].h):Math.max(b,hist[k].h);
     const side=x=>right?x>=b:x<=b;
     if([...a.t].some(x=>side(x)&&!t.has(x+d)))continue;
     if([...t].some(y=>side(y-d)&&!a.t.has(y-d)))continue;
     return {kind:"cycle",j,n,right,b};
    }
   }
   hist.push({q,h,t:new Set(t)});
   }
   if(m>=12)t.add(h);else t.delete(h);
   h+=(m%12>=6?1:-1);q=m%6;
  }return {kind:"timeout"};
 };
 const unresolved=p=>{stats.open++;residuals.push(p);return ".unresolved"};
 const walk=(p,cut,depth)=>{
  const target=targets.findIndex(t=>same(t,p));
  if(target>=0){stats.hits.push(target);return unresolved(p)}
  const path=targets.some(t=>extendsP(p,t)),c=classify(p,path);
  if(c.kind==="cycle"){stats.cycle++;stats.maxCycleEnd=Math.max(stats.maxCycleEnd,c.n);return `.closed (.cycle ${c.j} ${c.n-c.j} ${c.right} (${c.b}))`}
  if(c.kind==="hole"&&p.filter(x=>x===-1).length===1){stats.last++;stats.maxQuery=Math.max(stats.maxQuery,c.n);return `.closed (.last ${c.n} ${slot(c.s)})`}
  if(c.kind!=="hole"||(depth>=2&&!path))return unresolved(p);
  stats.split++;stats.maxQuery=Math.max(stats.maxQuery,c.n);
  const kids=Array.from({length:24},(_,m)=>{if(m%6>cut){stats.alias++;return ".unresolved"}const next=p.slice();next[c.s]=m;return walk(next,Math.max(cut,m%6+1),depth+1)});
  return `.split ${c.n} ${slot(c.s)} (byPartialMove [\n${kids.join(",\n")}\n])`;
 };
 const tree=walk(parent,4,0);
 if(stats.hits.length!==7||new Set(stats.hits).size!==7)throw Error(JSON.stringify(stats));
 const lean=`import CanonicalPartial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10Raw140
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
open BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent31FourHoleRoster

def parent : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨true,true,3⟩)
  | _,_ => none

def tree : PartialAudit := ${tree}

theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem parent_nohalt : weightedTNFNoAssignedHalt parent := by
  intro s; rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide
theorem parent_support : TNFSupport parent 4 := supportOK_sound _ _ (by decide)
theorem checked : canonicalCheck 10000 parent 4 tree = true := by decide
def before := canonicalResiduals parent 4 tree
theorem before_count : before.length = ${stats.open} := by decide
theorem root_sound : ∀ m, TNFQuotientCompatible parent m →
    WeightedBound 10000 m ∨ ∃ e ∈ before, TNFQuotientCompatible e.2 m :=
  canonicalSound 10000 parent 4 tree (by decide) parent_support parent_root parent_nohalt checked
#print axioms checked
#print axioms root_sound
end BB6.Agent10Raw140
`;
 const rle=p=>p.map(m=>m<0?"---":`${Math.floor(m/12)}${m%12>=6?"R":"L"}${String.fromCharCode(65+m%6)}`).join("").match(/....../g).join("_");
 return {lean,stats,residuals:residuals.map(rle),tables};
}
const g=generate();
for(const [name,content] of [["Raw140RootCut.lean",g.lean],["raw140-residuals.json",JSON.stringify({stats:g.stats,residuals:g.residuals},null,2)+"\n"]]){const p=path.join(__dirname,name);if(process.argv.includes("--check")){if(fs.readFileSync(p,"utf8")!==content)throw Error("mismatch: "+p)}else fs.writeFileSync(p,content)}
console.log(g.stats);
