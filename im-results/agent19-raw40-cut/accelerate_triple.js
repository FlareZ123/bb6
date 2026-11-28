'use strict';
const fs = require('node:fs');
const path = require('node:path');
const base = 'Raw40LateCrossingTriple';
function accelerate(files) {
  const table="1RB0LA_1RC1RA_0RD1RE_1LD1LA_---0RF_0RC0RF",sw=[2,1,0,3,4,5],tr=[];
  const rows=table.replaceAll("_","").match(/.../g);
  for(let i=0;i<12;i++){const a=rows[i];if(a!=="---")tr[2*sw[i>>1]+i%2]=[Number(a[0]),a[1]==="L",sw[a.charCodeAt(2)-65]];}
  const b=x=>x?"true":"false";
  const ns="BB6Coverage.Agent19Raw40LateCrossing.C1REM1096";
  const hdr=(imports)=>imports.map(i=>`import ${i}`).join("\n")+`\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nnamespace ${ns}\nopen BB6Coverage Agent42Crossing Agent19OrientedCrossing Agent50Zipper Agent13PackedZipper\n`;
  const footer=`\nend ${ns}\n`;
  const out={};
  out[base+"Table.lean"]=files[base+"Table.lean"].replace("import Raw40OrientedCrossing","import Raw40PackedCrossing").replace("def oriented : PartialMachine := orientPartial true true table",
    "def oriented : PartialMachine := fun slot => match slot.1.val,slot.2 with\n"+tr.map((a,i)=>a?`  | ${i>>1},${b(i%2)} => some (some ⟨${b(a[0])},${b(a[1])},${a[2]}⟩)`:"").filter(Boolean).join("\n")+
    `\n  | _,_ => none\n\ntheorem oriented_eq : oriented = orientPartial true true table := by\n  funext slot\n  rcases slot with ⟨q,a⟩\n  have hq := (by decide : ∀ q : Fin 6, q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5) q\n  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases a <;> rfl\n`);
  let q=2,l=0n,r=0n,t=0,i=0;
  const fmt=()=>`⟨${q},0x${l.toString(16)},0x${r.toString(16)}⟩`;
  let e=hdr([base+"Table"])+`def e0 : P := ${fmt()}\n`;
  const N=483904,K=16384;
  while(t<N){const t0=t,prev=i;i++;const stop=Math.min(N,t+K);while(t<stop){const a=tr[q*2+Number(l&1n)];if(!a)throw Error("unexpected query "+t);const [w,d,n]=a;const W=BigInt(w);if(d){l=(r&1n)+2n*W+4n*(l>>1n);r>>=1n;}else{l>>=1n;r=W+2n*r;}q=n;t++;}
    e+=`def e${i} : P := ${fmt()}\ntheorem step${i} : runP oriented ${t-t0} e${prev} = some e${i} := by decide +kernel\n`;
    e+=`theorem prefix${i} : runP oriented ${t} e0 = some e${i} := ${prev===0?"step1":`joinP prefix${prev} step${i}`}\n`;
  }
  if(q!==0||l!==0n)throw Error("entry");
  e+=`def entryP : P := e${i}\ntheorem entryRun : runP oriented 483904 (encode (initialZ true)) = some entryP := prefix${i}\n#print axioms entryRun\n`;
  out[base+"Entry.lean"]=e+footer;
  // Compress maximal repeated event substrings into exact list repetitions.
  const evList=s=>"["+Array.from(s,c=>"ev"+(c.charCodeAt(0)-65)).join(",")+"]";
  function wordExpr(s) {
    let parts=[],literal="",i=0,expanded="";
    const flush=()=>{if(literal){parts.push(evList(literal));expanded+=literal;literal="";}};
    while(i<s.length){let best=null;
      for(let k=1;k<=Math.min(64,Math.floor((s.length-i)/2));k++){let j=i+k;const w=s.slice(i,j);while(s.slice(j,j+k)===w)j+=k;const n=(j-i)/k,saving=(n-1)*k-3;if(n>=2&&saving>0&&(!best||saving>best.saving))best={w,n,saving,j};}
      if(best){flush();parts.push(`copies ${evList(best.w)} ${best.n}`);expanded+=best.w.repeat(best.n);i=best.j;}else{literal+=s[i++];}
    }
    flush();if(expanded!==s)throw Error("compression mismatch");return parts.length?parts.join(" ++ "):"[]";
  }
  let c=hdr([base+"Table"]);
  for(let n=0;n<48;n++)c+=`def ev${n} : Ev := ⟨${b(Math.floor(n/24)===1)},${b(Math.floor(n/12)%2===1)},${Math.floor(n/2)%6},${b(n%2)}⟩\n`;
  let count=0;
  for(const line of files[base+"Cells.lean"].split("\n")){let m=line.match(/^def (c\d+) : Cell := ⟨(true|false),(true|false),(true|false),eventsOf ("(?:[^"\\]|\\.)*")⟩$/);if(!m)continue;count++;let s=JSON.parse(m[5]);c+=`def ${m[1]} : Cell := ⟨${m[2]},${m[3]},${m[4]},${wordExpr(s)}⟩\n`;}
  if(count!==535)throw Error("cells "+count);
  c+=`def headCell : Cell := c336\ntheorem headOK : localOK oriented headCell (.active 0) := localB_sound oriented headCell (.active 0) (by rfl)\n`;
  out[base+"Cells.lean"]=c+footer;
  for(const suffix of ["Left","RightA","RightB"]){
    let s=files[base+suffix+".lean"];
    s=s.replace(/(theorem \w+OK : chain oriented [^\n]+ := by\n)  decide \+kernel/g,"$1  apply chainB_sound\n  rfl");
    s=s.replace(/(have ho : chain oriented [^\n]+ := by) decide \+kernel/g,"$1 apply chainB_sound; rfl");
    out[base+suffix+".lean"]=s;
  }
  let fin=files[base+".lean"].split("theorem checkedCert")[0];
  fin=fin.replace("open BB6Coverage Agent42Crossing Agent19OrientedCrossing Agent50Zipper","open BB6Coverage Agent42Crossing Agent19OrientedCrossing Agent50Zipper Agent13PackedZipper");
  fin+=`theorem entryChecked : runP oriented 483904 (encode (initialZ true)) = some (packedGoal cert) := by
  rw [entryRun]
  rfl
theorem headLive : cert.head.events ≠ [] := by decide +kernel
theorem inputChecked : inputBlank cert := by decide +kernel
theorem recurrenceChecked : recOK cert := by decide +kernel

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_oriented_packed true true table cert 483904
    (by rw [← oriented_eq]; exact bankOK) headLive inputChecked recurrenceChecked
    (by rw [← oriented_eq]; exact entryChecked) m hm
#print axioms bankOK
#print axioms never
`+footer;
  out[base+".lean"]=fin;
  return out;
}
const names = ['Table','Entry','Cells','Left','RightA','RightB',''].map(x=>base+x+'.lean');
const files = Object.fromEntries(names.map(n=>[n,fs.readFileSync(path.join(__dirname,n),'utf8')]));
const out=accelerate(files);
for(const [n,s] of Object.entries(out)) fs.writeFileSync(path.join(__dirname,n),s);
