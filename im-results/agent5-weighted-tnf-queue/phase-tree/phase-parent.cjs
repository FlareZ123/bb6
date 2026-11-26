"use strict";
// node phase-parent.cjs <source export.json> <output directory> <root indices...>
const fs=require("node:fs"),path=require("node:path");
const {classify,bank,pairs}=require("../coarse-pair.cjs");
const {solve,search,mitmCert}=require("../q0-open-automata.cjs");
const known=Object.values(JSON.parse(fs.readFileSync(path.join(__dirname,"../q0-open-automata.json"),"utf8")));
const cache=new Map(known.map(c=>[c.table,c]));
const moves=Array.from("ABCDEF").flatMap(q=>Array.from("01").flatMap(w=>Array.from("LR").map(d=>w+d+q)));
function run(table,limit){let q=0,l=0n,r=0n,h=0;
 for(let n=0;n<=limit;n++){let i=2*q+Number(r&1n),m=table[i];if(m==="---")return {n,i,h};if(n===limit)return {h};
 let w=BigInt(m[0]);q=m.charCodeAt(2)-65;if(m[1]==="R"){l=(l<<1n)|w;r>>=1n;h++}else{r=((r>>1n)<<2n)|(w<<1n)|(l&1n);l>>=1n;h--}}
}
function cert(t){
 let s=t.join("");if(cache.has(s))return cache.get(s);
 for(const [l,r] of pairs){let c=mitmCert(s,bank[l],bank[r]);if(c){cache.set(s,c);return c}}
 let c=solve(s,6,"run",false,100000,1,2)||solve(s,6,"run",true,100000,1,2)||search(s);
 if(c)cache.set(s,c);return c;
}
function discover(row,cap=2000000){let nodes=0,bound=0,stats={side:0,dfa:0,last:0,split:0,open:0},open=new Set();
 function go(a,holes,cut){if(++nodes>cap)throw Error("node cap");let c=classify(a,256);
  if(c.kind==="open"){let w=cert(a);if(w){stats.dfa++;return ["d",w]}
   c=classify(a,1500);if(c.kind==="open"){let z=run(a,5000);if(z.n!==undefined)c={kind:"split",n:z.n,i:z.i};
    else{stats.open++;open.add(a.join(""));return ["o",a.join("")]}}}
  if(c.kind==="side"){stats.side++;let d=c.d==="R"?1:-1;return ["s",c.e,c.p,d,run(a,c.e).h-d*c.k]}
  bound=Math.max(bound,c.n+6);
  if(holes===1){stats.last++;return ["h",c.n,c.i]}
  stats.split++;return ["x",c.n,c.i,cut,moves.slice(0,4*Math.min(6,cut+1)).map((m,j)=>{let b=a.slice();b[c.i]=m;return go(b,holes-1,Math.max(cut,1+(j>>2)))})];
 }
 let a=row.table.replaceAll("_","").match(/.{3}/g);
 let tree=go(a,row.holes,row.fresh);return {root:a.join(""),tree,bound,stats:{nodes,...stats},open:[...open]};
}
const bit=x=>x?"true":"false",slot=i=>"("+Math.floor(i/2)+","+bit(i%2)+")";
function move(m){return "⟨"+bit(m[0]==="1")+","+bit(m[1]==="R")+","+(m.charCodeAt(2)-65)+"⟩"}
function tab(t){return "fun s => match s with\n"+t.match(/.{3}/g).map((m,i)=>"  | "+slot(i)+" => "+(m==="---"?"none":"some (some "+move(m)+")")).join("\n")+"\n  | _ => none"}
function certLean(c){
 const stack=s=>"⟨#["+s.pop.map(es=>"["+es.map(([b,i])=>"("+bit(b)+","+i+")").join(",")+"]").join(",")+"],#["+s.push.map(([x,y])=>"("+x+","+y+")").join(",")+"]⟩";
 const trie=xs=>!xs.length?".empty":xs.length===1&&xs[0]===0?".leaf":"(.branch "+trie(xs.filter(x=>x%2===0).map(x=>Math.floor(x/2)))+" "+trie(xs.filter(x=>x%2).map(x=>Math.floor(x/2)))+")";
 let rows=Array.from({length:12},(_,i)=>trie(c.rows.filter(([q,a])=>2*q+a===i).map(([q,a,l,r])=>r+c.right.pop.length*l).sort((a,b)=>a-b)));
 return "⟨"+stack(c.left)+","+stack(c.right)+",#["+rows.join(",")+"]⟩";
}
function emit(t){
 if(t[0]==="s")return "(.side "+t[1]+" "+t[2]+" "+bit(t[3]>0)+" ("+t[4]+"))";
 if(t[0]==="d")return "(.automata "+certLean(t[1])+")";
 if(t[0]==="h")return "(.last "+t[1]+" "+slot(t[2])+")";
 if(t[0]==="x")return "(split "+t[1]+" "+slot(t[2])+" "+t[3]+" #["+t[4].map(emit).join(",\n")+"])";
 throw Error("open leaf in closed tree");
}
function size(t){return 1+(t[0]==="x"?t[4].reduce((a,c)=>a+size(c),0):0)}
function long(t){return ((t[0]==="h"||t[0]==="x")&&t[1]>500)||(t[0]==="x"&&t[4].some(long))}
function shards(idx,d,out,threshold=30){if(d.open.length)throw Error("open root");
 const files=[],B=d.bound,common="set_option maxHeartbeats 0\nset_option maxRecDepth 100000\nopen BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree\n";
 function write(name,body){fs.writeFileSync(path.join(out,name+".lean"),body);files.push(name)}
 function rec(tr,p,pt,pm){
  let name="PhaseShard"+idx+"_"+p,ns="namespace "+name+"\n",end="end "+name+"\n";
  let imp=pm?"import "+pt+"Base\n":"import PhaseTree\n";
  let decl="def parent : PartialMachine := "+(pm?"refine "+pt+".parent "+slot(pm[0])+" (some "+move(pm[1])+")":tab(d.root))+"\n";
  let typ="theorem safe : ∀ m, compatible parent m → WeightedBound "+B+" m := ";
  if(size(tr)<=threshold&&!long(tr)){
   write(name,imp+common+ns+decl+"def cert : Tree := "+emit(tr)+"\n"+typ+"sound "+B+" parent cert (by decide) (by decide)\n#print axioms safe\n"+end);return name;
  }
  if(tr[0]==="h"){
   write(name,imp+"import PhaseFastHole\n"+common+ns+decl+typ+"BB6.Agent5PhaseFastHole.last_safe "+B+" parent "+tr[1]+" "+slot(tr[2])+" (by decide) (by decide) (by decide)\n#print axioms safe\n"+end);return name;
  }
  if(tr[0]!=="x")throw Error("unexpected shard");
  write(name+"Base",imp+common+ns+decl+end);
  let [_,n,i,cut,kids]=tr,children=kids.map((k,j)=>rec(k,p+"_"+j,name,[i,moves[j]]));
  let method=n>500?"BB6.Agent5PhaseFastHole.fast_split_safe":"split_safe";
  let proof=children.map(x=>"import "+x+"\n").join("")+(n>500?"import PhaseFastHole\n":"")+common+ns+typ+"by\n  apply "+method+" "+B+" parent "+n+" "+slot(i)+" "+cut+" (by decide) (by decide) (by decide) (by decide)\n  intro mv hv\n  rcases mv with ⟨w,r,q⟩\n  rcases statesCases q with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r\n";
  for(let j=0;j<24;j++)proof+=j<children.length?"  · exact "+children[j]+".safe\n":"  · omega\n";
  write(name,proof+"#print axioms safe\n"+end);return name;
 }
 let target=rec(d.tree,"r",null,null);fs.writeFileSync(path.join(out,"PhaseShard"+idx+".files"),files.join("\n")+"\n");return {target,files:files.length};
}
if(require.main===module){
 let [input,out,...ids]=process.argv.slice(2);fs.mkdirSync(out,{recursive:true});let data=JSON.parse(fs.readFileSync(input,"utf8"));
 for(let idx of ids.map(Number)){let t=Date.now(),d=discover(data.active[idx]);let z=d.open.length?{}:shards(idx,d,out);
 fs.writeFileSync(path.join(out,"parent"+idx+".json"),JSON.stringify(d));console.log(JSON.stringify({idx,root:d.root,bound:d.bound,stats:d.stats,open:d.open,...z,ms:Date.now()-t}))}
}
module.exports={discover,shards,certLean};
