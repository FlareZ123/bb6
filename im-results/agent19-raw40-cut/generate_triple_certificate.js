'use strict';
const fs = require('node:fs');
function generate() {
  const ns="BB6Coverage.Agent19Raw40LateCrossing.C1REM1096";
  const base="Raw40LateCrossingTriple", dir="im-results/agent19-raw40-cut/";
  const files={};
  const table="1RB0LA_1RC1RA_0RD1RE_1LD1LA_---0RF_0RC0RF";
  const rows=table.replaceAll("_","").match(/.../g), swap=[2,1,0,3,4,5], tr=new Map();
  for(let i=0;i<12;i++)if(rows[i]!=="---"){
    const a=rows[i];tr.set(2*swap[i>>1]+i%2,[Number(a[0]),a[1]==="L"?1:-1,swap[a.charCodeAt(2)-65]]);
  }
  const hdr=(imports)=>imports.map(i=>`import ${i}`).join("\n")+`\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nnamespace ${ns}\nopen BB6Coverage Agent42Crossing Agent19OrientedCrossing Agent50Zipper\n`;
  const footer=`\nend ${ns}\n`;
  const b=(x)=>x?"true":"false";
  const tableRows=rows.map((a,i)=>a==="---"?"":`  | ${i>>1},${b(i%2)} => some (some ⟨${b(Number(a[0]))},${b(a[1]==="R")},${a.charCodeAt(2)-65}⟩)`).filter(Boolean).join("\n");
  files[base+"Table.lean"]=hdr(["Raw40OrientedCrossing"])+`def table : PartialMachine := fun slot => match slot.1.val,slot.2 with\n${tableRows}\n  | _,_ => none\ndef oriented : PartialMachine := orientPartial true true table\n`+footer;
  let l=[],r=[],q=2,h=0,entry=[],t=0;
  function move(){
    const v=tr.get(2*q+(l.at(-1)||0));if(!v)throw Error("missing transition "+t);
    const [w,d,n]=v;l.pop();if(d===1){l.push(w,r.pop()||0)}else r.push(w);q=n;h+=d;t++;
  }
  function checkpoint(){entry.push({t,q,h,l:[...l].reverse().join(""),r:[...r].reverse().join("")})}
  checkpoint();while(t<483904){move();if(t%2048===0||t===483904)checkpoint()}
  if(q!==0||h!==-1298)throw Error("entry");
  let es=hdr([base+"Table"])+`def bits (s : String) : List Bool := s.toList.map (fun c => c == '1')\ndef e0 : Z := initialZ true\n`;
  for(let i=1;i<entry.length;i++){
    const v=entry[i],prev=entry[i-1];es+=`def e${i} : Z := ⟨${v.q},${v.h},bits "${v.l}",bits "${v.r}"⟩\n`;
    es+=`theorem step${i} : zrun oriented ${v.t-prev.t} e${i-1} = some e${i} := by decide +kernel\n`;
    es+=i===1?`theorem prefix1 : zrun oriented ${v.t} e0 = some e1 := step1\n`:`theorem prefix${i} : zrun oriented ${v.t} e0 = some e${i} := join prefix${i-1} step${i}\n`;
  }
  const last=entry.length-1;
  es+=`def entryZ : Z := e${last}\ntheorem entryRun : zrun oriented 483904 (initialZ true) = some entryZ := prefix${last}\n#print axioms entryRun\n`;
  files[base+"Entry.lean"]=es+footer;
  const start=h,tape=new Set(),events=new Map();
  let lo=Math.min(h,h-l.length+1),hi=h+r.length;
  for(let i=0;i<l.length;i++)if(l[l.length-1-i])tape.add(h-i);
  for(let i=0;i<r.length;i++)if(r[r.length-1-i])tape.add(h+i+1);
  const init=new Set(tape);
  function ev(x,e){if(!events.has(x))events.set(x,[]);events.get(x).push(e)}
  const code=(enter,d,q,w)=>24*enter+12*(d===1?1:0)+2*q+w;
  for(let i=0;i<271120;i++){
    const a=tr.get(q*2+Number(tape.has(h)));if(!a)throw Error("hole at epoch "+i);
    const [w,d,n]=a;ev(h,code(0,d,n,w));if(w)tape.add(h);else tape.delete(h);h+=d;q=n;ev(h,code(1,d,n,0));lo=Math.min(lo,h);hi=Math.max(hi,h);
  }
  if(h!==-1634||q!==0)throw Error("epoch");
  const uniq=[],ids=new Map(),positions=new Map();
  for(let x=lo;x<=hi;x++){
    const c={bit:Number(init.has(x)),out:Number(tape.has(x)),mark:Number(x===h),events:events.get(x)||[]};
    const key=JSON.stringify(c);if(!ids.has(key)){ids.set(key,uniq.length);uniq.push(c)}positions.set(x,ids.get(key));
  }
  const head=positions.get(start),left=[],right=[];
  for(let x=start-1;x>=lo;x--)left.push(positions.get(x));
  for(let x=start+1;x<=hi;x++)right.push(positions.get(x));
  const cuts=[0,1,225,907,1003,1253,1269,right.length];
  if(cuts.at(-1)<=1269)throw Error("cuts");
  const edge=(i,d)=>uniq[i].events.filter(n=>{const en=Math.floor(n/24),dr=Math.floor(n/12)%2;return (en?1-dr:dr)===d}).map(n=>[Math.floor(n/12)%2,Math.floor(n/2)%6]);
  const eq=(a,b)=>JSON.stringify(a)===JSON.stringify(b);
  for(const [d,seq] of [[0,left],[1,right]]){
    let prev=head;for(const i of seq){if(!eq(edge(prev,d),edge(i,1-d)))throw Error("edge mismatch");prev=i}
    if(edge(prev,d).length)throw Error("unclosed edge");
  }
  let cs=hdr([base+"Table"])+`def eventCode (c : Char) : Ev :=\n  let n := c.toNat - 65\n  ⟨n / 24 == 1, n / 12 % 2 == 1, ⟨n / 2 % 6, Nat.mod_lt _ (by decide)⟩, n % 2 == 1⟩\ndef eventsOf (s : String) : List Ev := s.toList.map eventCode\n`;
  for(let i=0;i<uniq.length;i++){const c=uniq[i];const enc=String.fromCharCode(...c.events.map(x=>65+x));cs+=`def c${i} : Cell := ⟨${b(c.bit)},${b(c.out)},${b(c.mark)},eventsOf ${JSON.stringify(enc)}⟩\n`;}
  cs+=`def headCell : Cell := c${head}\ntheorem headOK : localOK oriented headCell (.active 0) := by decide +kernel\n`;
  files[base+"Cells.lean"]=cs+footer;
  let segments=[],groupStats=[];
  function genChain(name,seq,d,initial,final,externalExit){
    const ds=b(d),parts=[];let i=0;
    while(i<seq.length){
      let j=i+1;while(j<seq.length&&seq[j]===seq[i])j++;
      if(j-i>=2){parts.push({arr:seq.slice(i,j),rep:true});i=j;continue}
      j=i+1;while(j<seq.length&&j-i<6&&(j+1===seq.length||seq[j]!==seq[j+1]))j++;
      parts.push({arr:seq.slice(i,j),rep:false});i=j;
    }
    let s="",a=initial;const arr=[],bounds=[initial];
    for(let k=0;k<parts.length;k++){
      const p=parts[k],z=name+"B"+k,bb=k+1===parts.length?final:`(edge c${p.arr.at(-1)} ${ds})`;
      const literal="["+p.arr.map(i=>"c"+i).join(",")+"]";
      s+=`def ${z} : List Cell := ${p.rep?`copies [c${p.arr[0]}] ${p.arr.length}`:literal}\n`;
      s+=`theorem ${z}OK : chain oriented ${ds} ${a} ${z} ${bb} := by\n`;
      if(p.rep){s+=`  have he : ${bb} = ${a} := by decide +kernel\n  have ho : chain oriented ${ds} ${a} [c${p.arr[0]}] ${a} := by decide +kernel\n  simpa only [he] using (chain_copies oriented ${ds} ${a} [c${p.arr[0]}] ho ${p.arr.length})\n`;}
      else s+=`  decide +kernel\n`;
      arr.push(z);bounds.push(bb);a=bb;
    }
    // Named suffixes share the proof DAG and avoid elaborating a deeply nested conjunction.
    for(let k=arr.length-1;k>=0;k--){
      const n=name+"Tail"+k;
      s+=`def ${n} : List Cell := ${arr[k]}${k+1===arr.length?"":` ++ ${name}Tail${k+1}`}\n`;
      s+=`theorem ${n}OK : chain oriented ${ds} ${bounds[k]} ${n} ${final} := ${k+1===arr.length?arr[k]+"OK":`chain_append oriented ${ds} _ _ _ _ _ ${arr[k]}OK ${name}Tail${k+1}OK`}\n`;
    }
    s+=`def ${name} : List Cell := ${name}Tail0\ntheorem ${name}OK : chain oriented ${ds} ${initial} ${name} ${final} := ${name}Tail0OK\n`;
    groupStats.push([name,seq.length,parts.length,parts.filter(p=>p.rep).length]);
    return s;
  }
  files[base+"Left.lean"]=hdr([base+"Cells"])+genChain("leftCells",left,0,"(edge headCell false)","[]")+footer;
  let rightSrc=hdr([base+"Cells"]),rightSrc2=hdr([base+"Cells"]);
  for(let k=0;k<cuts.length-1;k++){
    const a=cuts[k],z=cuts[k+1],seq=right.slice(a,z),pump=k%2===1;
    const prev=a===0?head:right[a-1],inEdge=a===0?"(edge headCell true)":`(edge c${prev} true)`,outEdge=k===cuts.length-2?"[]":`(edge c${seq.at(-1)} true)`;
    if(pump&&!eq(edge(prev,1),edge(seq.at(-1),1)))throw Error("bad pump");
    let s=genChain("right"+k,seq,1,inEdge,outEdge);
    s+=`def seg${k} : Segment := ⟨right${k},${b(pump)},${outEdge}⟩\ntheorem pump${k} : seg${k}.pump = true → ${inEdge} = seg${k}.exit := by decide +kernel\n`;
    if(k<4)rightSrc+=s;else rightSrc2+=s;
    segments.push(k);
  }
  files[base+"RightA.lean"]=rightSrc+footer;
  files[base+"RightB.lean"]=rightSrc2+footer;
  let fin=hdr([base+"Entry",base+"Left",base+"RightA",base+"RightB"]);
  fin+=`def cert : Certificate := ⟨leftCells,headCell,[${segments.map(k=>"seg"+k).join(",")}]⟩\n`;
  fin+=`theorem bankOK : certOK oriented cert := by\n  refine ⟨headOK,leftCellsOK,?_⟩\n  exact ⟨${segments.flatMap(k=>["right"+k+"OK","pump"+k]).join(",")},rfl⟩\n`;
  fin+=`theorem checkedCert : checkedFrom oriented cert (initialZ true) 483904 (-1298) := by\n  refine ⟨bankOK,?_,?_,?_,?_⟩\n  · decide +kernel\n  · decide +kernel\n  · decide +kernel\n  · unfold entryOKFrom\n    rw [entryRun]\n    decide +kernel\n`;
  fin+=`theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=\n  never_oriented true true table cert 483904 (-1298) checkedCert m hm\n#print axioms bankOK\n#print axioms never\n`;
  files[base+".lean"]=fin+footer;
  return {files,stats:{entryCheckpoints:entry.length,lo,hi,distinct:uniq.length,eventCount:uniq.reduce((s,c)=>s+c.events.length,0),groups:groupStats,sourceSizes:Object.fromEntries(Object.entries(files).map(([k,v])=>[k,v.length]))}};
}
const {files,stats}=generate();
for (const [path,source] of Object.entries(files)) fs.writeFileSync(require('node:path').join(__dirname,path),source);
console.log(JSON.stringify(stats,null,2));
