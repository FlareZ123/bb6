"use strict";
// Reuse the exact q0 export, original first-hole search, and finite-stack
// certificate bank. The generator is untrusted: Lean checks every subtree.
const fs=require("node:fs"),path=require("node:path");
const base="../agent5-weighted-tnf-queue/";
const {find,bank}=require(base+"coarse-pair.cjs");
const {sourceMitmCert}=require(base+"q0-source-mitm-cert.cjs");
const data=require(base+"q0-export/pilot-0-100-fuel-1000000.json");
const bankCerts=require(base+"q0-open-automata.json");
const root=data.active[26], B=200;
if(root.table!=="1RB1RD_1RC0RE_0LA0RF_1LA1LD_---0LA_------"||root.holes!==3||root.fresh!==6)throw Error("root identity");
const {tree,n}=find(root,true);
if(!tree||n!==361)throw Error("tree size");
const lookup=new Map(Object.entries(bankCerts).filter(([id])=>id.startsWith("R26L")).map(([id,c])=>[c.table,c]));
const moves=Array.from("ABCDEF").flatMap(q=>Array.from("01").flatMap(w=>Array.from("LR").map(d=>w+d+q)));
const bit=b=>b?"true":"false", arr=xs=>"#["+xs.join(",")+"]", ls=xs=>"["+xs.join(",")+"]";
const slot=n=>"("+Math.floor(n/2)+","+bit(n%2)+")";
const move=n=>"⟨"+bit(Math.floor(n%4/2))+","+bit(n%2)+","+Math.floor(n/4)+"⟩";
function head(a,n){let l=0n,r=0n,q=0,h=0;for(let i=0;i<n;i++){let t=a[2*q+Number(r&1n)];if(t==="---")throw Error("early hole");let w=BigInt(t[0]);if(t[1]==="R"){l=(l<<1n)|w;r>>=1n;h++}else{r=((r>>1n)<<2n)|(w<<1n)|(l&1n);l>>=1n;h--}q=t.charCodeAt(2)-65;}return h}
function trie(xs){if(xs.length===0)return ".empty";if(xs.length===1&&xs[0]===0)return ".leaf";return "(.branch "+trie(xs.filter(x=>x%2===0).map(x=>Math.floor(x/2)))+" "+trie(xs.filter(x=>x%2===1).map(x=>Math.floor(x/2)))+")"}
function stack(s){return "⟨"+arr(s.pop.map(es=>ls(es.map(([b,i])=>"("+bit(b)+","+i+")"))))+","+arr(s.push.map(([x,y])=>"("+x+","+y+")"))+"⟩"}
function cert(c){let rows=Array.from({length:12},(_,i)=>trie(c.rows.filter(([q,b])=>2*q+b===i).map(([q,b,l,r])=>r+c.right.pop.length*l).sort((a,b)=>a-b)));return "⟨"+stack(c.left)+","+stack(c.right)+","+arr(rows)+"⟩"}
const counts={side:0,last:0,auto:0,split:1}, seen=new Set();
function emit(t,a,f){if(t[0]==="s"){counts.side++;const [,d,e,p,k]=t,b=head(a,e)+(d==="R"?-k:k);return "(.side "+e+" "+p+" "+bit(d==="R")+" ("+b+"))"}if(t[0]==="p"||t[0]==="o"){counts.auto++;const c=t[0]==="p"?sourceMitmCert(a.join(""),bank[t[1]],bank[t[2]]):lookup.get(t[1]);if(!c||c.table!==a.join(""))throw Error("missing exact cert");if(t[0]==="o")seen.add(t[1]);return "(.automata "+cert(c)+")"}if(t[0]!=="h")throw Error("bad tree");if(!t[3].length){counts.last++;return "(.last "+t[1]+" "+slot(t[2])+")"}counts.split++;if(t[3].length!==24)throw Error("incomplete branch");return "(split "+t[1]+" "+slot(t[2])+" "+f+" #[\n"+t[3].map((kid,j)=>{let b=a.slice();b[t[2]]=moves[j];return emit(kid,b,Math.max(f,1+(j>>2)))}).join(",\n")+"])"}
const entries=root.table.replaceAll("_","").match(/.{3}/g);
function table(es){return "(fun s => match s.1.val,s.2 with\n"+es.map((x,i)=>x==="---"?null:"  | "+Math.floor(i/2)+","+bit(i%2)+" => some (some ⟨"+bit(x[0]==="1")+","+bit(x[1]==="R")+","+(x.charCodeAt(2)-65)+"⟩)").filter(x=>x!==null).join("\n")+"\n  | _,_ => none)"}
if(tree[0]!=="h"||tree[3].length!==24)throw Error("root split");
const [,qn,qs,kids]=tree, f=root.fresh;
let out="import PhaseTree\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nnamespace BB6.Agent47Root26\nopen BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree\ndef parent : PartialMachine := "+table(entries)+"\n";
for(let i=0;i<kids.length;i++){let b=entries.slice();b[qs]=moves[i];out+="def cert"+i+" : Tree := "+emit(kids[i],b,Math.max(f,1+(i>>2)))+"\n";out+="theorem checked"+i+" : check 200 (refine parent "+slot(qs)+" (some "+move(i)+")) cert"+i+" = true := by decide +kernel\n";out+="theorem safe"+i+" : ∀ m, compatible (refine parent "+slot(qs)+" (some "+move(i)+")) m → WeightedBound 200 m := sound 200 _ cert"+i+" (by decide) checked"+i+"\n"}
out+="theorem safe : ∀ m, compatible parent m → WeightedBound 200 m := by\n  apply split_safe 200 parent "+qn+" "+slot(qs)+" "+f+" (by decide) (by decide +kernel) (by decide) (by decide)\n  intro mv h\n  rcases mv with ⟨w,r,q⟩\n  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | "+kids.map((_,i)=>"exact safe"+i).join(" | ")+"\n\ntheorem cover : Cover (WeightedBound 200) parent := .leaf _ safe\n#print axioms safe\n#print axioms cover\nend BB6.Agent47Root26\n";
if(counts.side!==159||counts.last!==101||counts.auto!==86||counts.split!==15||seen.size!==13)throw Error(JSON.stringify(counts));
fs.writeFileSync(process.argv[2]||path.join(__dirname,"Root26Lean.lean"),out);
console.log(JSON.stringify({root:root.table,n,bound:B,counts,openBank:seen.size,chars:out.length}));
