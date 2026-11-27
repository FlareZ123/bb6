// Regenerate the complete sibling-28 or sibling-81 proof from the sibling-86 proof schema.
// Each proposed affine path and every finite root chunk is checked in Lean.
const fs=require("fs"),path=require("path"),{execFileSync}=require("child_process");
const {rule,exits,tables}=require("./generate_raw140_variant_transfer.js");
const id=Number(process.argv[2]||28);
const [a,f,tend,p]=({28:[21,0,6896,39],81:[23,17,6896,39]})[id];
const N="Raw140"+id,M="M"+id;
const tab=[7,a,11,12,15,1,6,18,4,17,f,24];
tables[id]=tab;
const recipes=JSON.parse(execFileSync("python3",["-c",
"import json,raw14086_local as r\nr.TAB="+JSON.stringify(tab)+"\nr.E=r.exits(r.TAB)\n"+
(id===81?"for n in ['cSeed','b62','b6221','b6405','a542','a1121','a1155','c315','c3242']: r.S.pop(n)\nfor n,goal in [('b62542',r.A('3^p+31 2','')),('a5215',r.A('3^p+30 2','2')),('c35221',r.B('5^p+34',''))]: r.S[n]=(r.S[n][0],goal)\n":"")+
"print(json.dumps({n:dict(start=s,end=t,path=r.recipe(s,t)) for n,(s,t) in r.S.items()}))"
],{cwd:__dirname,encoding:"utf8"}));
const write=(s,t)=>fs.writeFileSync(path.join(__dirname,N+s+".lean"),t);
const trans=c=>"some ⟨"+Boolean(c&2)+","+Boolean(c&1)+","+Math.floor(c/4)+"⟩";
let local="import Raw140ExtraCore\nnamespace "+N+"Local\nopen BB6BlockFAR Raw140Orbit Raw140Extra\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\ndef "+M+" : Table := fill ("+trans(a)+") ("+trans(f)+")\n";
for(const [name,{start,end,path:seq}] of Object.entries(recipes)){
 const [q,d,L,R]=start,[q1,d1,L1,R1]=end;
 const tokens=seq.map(([s,[x,y]])=>s+(x?"^p"+(y?"+"+y:""):(y===1?"":"^"+y))).join(" ");
 local+=rule(name,id,L,R,q,d,L1,R1,q1,d1,tokens)+"\n";
}
write("Local",local+"end "+N+"Local\n");
const E=exits(id);
let q=2,d=1,L=[[6,1]],R=[],t=2,k=0,pt=t,pk=k,roots=[],chunks=[];
const repr=s=>"["+s.map(([x,n])=>"(S "+x+","+n+")").join(",")+"]";
const state=()=> "⟨"+q+","+Boolean(d)+","+repr(L)+","+repr(R)+"⟩";
roots.push(state());
while(t<tend){
 let src=d?R:L;
 let [b,n]=src.length?src[0]:[0,1];
 const e=E[[q,d,b]];
 if(!e)throw Error("undefined root");
 const [q1,d1,w,c]=e;
 if(q1!==q||d1!==d)n=1;
 if(src.length){src[0][1]-=n;if(!src[0][1])src.shift();}
 const dst=d1?L:R;
 if(dst.length||w){if(dst.length&&dst[0][0]===w)dst[0][1]+=n;else dst.unshift([w,n]);}
 q=q1;d=d1;t+=n*c;k++;
 if(k-pk===256||t===tend){chunks.push([k-pk,t-pt]);roots.push(state());pt=t;pk=k;}
}
if(t!==tend||q!==0||d!==1||JSON.stringify(L)!==JSON.stringify([[3,p],[2,1]])||JSON.stringify(R)!=="[[2,1]]")throw Error("root mismatch");
let entry="import "+N+"D\nimport Raw140Sweep\nnamespace "+N+"\nopen BB6BlockFAR Raw140Orbit Raw140Extra "+N+"Local Raw140Sweep\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n";
roots.forEach((s,i)=>entry+="def rootS"+i+" : RState := "+s+"\n");
chunks.forEach(([n,c],j)=>entry+="theorem rootE"+(j+1)+" : execute "+M+" "+n+" rootS"+j+" = some ("+c+",rootS"+(j+1)+") := by decide +kernel\n");
entry+="theorem entry : run "+M+" "+tend+" primBlank = some (A2 "+p+") := by\n  have h0 : run "+M+" 2 primBlank = some rootS0.prim := run_ext "+M+" ext _ _ _ base_start\n";
chunks.forEach(([n,c],j)=>entry+="  have h"+(j+1)+" := join h"+j+" (execute_sound "+M+" "+n+" "+c+" rootS"+j+" rootS"+(j+1)+" rootE"+(j+1)+")\n");
entry+="  exact h"+chunks.length+"\n#print axioms entry\nend "+N+"\n";
write("Entry",entry);
for(const suffix of ["D","C","B","Cover"]){
 let s=fs.readFileSync(path.join(__dirname,"Raw14086"+suffix+".lean"),"utf8")
 .replace(/Raw14086(?!Arithmetic)/g,N).replace(/M86/g,M).replace(/6892/g,String(tend)).replace(/\(\.a2,39\)/g,"(.a2,"+p+")").replace("[7,23,11,12,15,1,6,18,4,17,11,24]","["+tab.join(",")+"]");
 for(const name of Object.keys(recipes)){
  s=s.replace(new RegExp("\\b"+name+" \\((?!p :=)([^()]+)\\)","g"),(m,x)=>x.includes("-")?name+" (p := "+x+")":m);
 }
 write(suffix,s);
}
if(id===81)execFileSync("python3",[path.join(__dirname,"patch_raw140_81.py")],{stdio:"inherit"});
console.log("Generated "+Object.keys(recipes).length+" local rules, "+k+" root macro events.");
