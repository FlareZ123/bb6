'use strict';
// Exact compressed-state one-edge certificates, independent per shard.
// Each step is checked by the Lean kernel, not trusted from JS.
const fs=require('node:fs'), path=require('node:path');
const read=p=>fs.readFileSync(path.join(__dirname,p),'utf8');
function exactEngine(engineText,replayText){
 const match=replayText.match(/const replacements = ({[\s\S]*?});\nlet code/);
 if(!match)throw Error("replacement table");
 const replacements=new Function("return "+match[1])();
 for(const [oldText,newText] of Object.entries(replacements)){
  if(!engineText.includes(oldText))throw Error("missing replacement");
  engineText=engineText.split(oldText).join(newText);
 }
 const start=engineText.indexOf("const tokenRE"),end=engineText.indexOf("const machineMatch");
 if(start<0||end<start)throw Error("engine boundaries");
 return new Function(engineText.slice(start,end)+"\nreturn {parseState,rleStep,rleStepBound,stable};")();
}
const item=x=>x.t==="z"?".z "+x.c:x.t==="d"?".d "+x.v:".k "+x.r+" "+x.c;
const seg=([r,c])=>"("+r+", "+c+")";
function literal(s){
 const list=(xs,f)=>"["+xs.map(f).join(", ")+"]";
 const ls=s.ls.t==="raw"?".raw "+list(s.ls.items,item):".clean "+s.ls.c0+" "+list(s.ls.segs,seg)+" "+s.ls.bot;
 return "⟨."+s.mode+", "+ls+", "+list(s.R,item)+", "+s.halted+"⟩";
}
const open="open Mathlib Relation Nat Turing BusyBeaver BusyBeaver.RleStackEngine\nnamespace BB6.Agent17.RleCounted\nset_option maxHeartbeats 0\nset_option maxRecDepth 20000\n";
const close="\nend BB6.Agent17.RleCounted\n";
function balanced(names){
 if(names.length===1)return names[0];
 const m=Math.floor(names.length/2);
 return "(CountPath.trans "+balanced(names.slice(0,m))+" "+balanced(names.slice(m))+")";
}
// Suffix DAG: each repeated list tail is emitted once per independent shard.
// Only shared convergence points become definitions; singly-used chains inline.
function listsFor(states){
 const nodes=[null], table=new Map();
 function intern(xs,tag){
  let id=0;
  for(let i=xs.length-1;i>=0;i--){
   const h=(tag==="i"?item:seg)(xs[i]),key=tag+"|"+h+"|"+id;
   let n=table.get(key);
   if(n===undefined){
    n=nodes.length;table.set(key,n);
    nodes.push({id:n,tag,h,tail:id,refs:0,len:id?nodes[id].len+1:1});
    if(id)nodes[id].refs++;
   }
   id=n;
  }
  if(id)nodes[id].refs++;
  return id;
 }
 const ids=states.map(s=>[intern(s.ls.t==="raw"?s.ls.items:s.ls.segs,s.ls.t==="raw"?"i":"s"),intern(s.R,"i")]);
 const chosen=n=>n&&nodes[n].refs>1&&nodes[n].len>=2;
 function render(n,force=false){
  if(!n)return "[]";
  if(chosen(n)&&!force)return "tail_"+n;
  return "("+nodes[n].h+" :: "+render(nodes[n].tail)+")";
 }
 const defs=nodes.slice(1).filter(n=>chosen(n.id)).map(n=>"private def tail_"+n.id+" : List "+(n.tag==="i"?"Item":"(Nat × Nat)")+" := "+render(n.id,true));
 const encoded=states.map((s,i)=>{
  const [l,r]=ids[i];
  const ls=s.ls.t==="raw"?".raw "+render(l):".clean "+s.ls.c0+" "+render(l)+" "+s.ls.bot;
  return "⟨."+s.mode+", "+ls+", "+render(r)+", "+s.halted+"⟩";
 });
 return {defs,encoded};
}
function generate(roots,engineText,replayText,counts,outdir,chunkSize=500){
 if(!Number.isInteger(chunkSize)||chunkSize<25||chunkSize>1000)throw Error("invalid chunk size");
 const {parseState,rleStep,rleStepBound,stable}=exactEngine(engineText,replayText);
 const endpoints=["import RleEdgePath\n"+open],imports=["RleEdgePath","RleEdgeEndpoints"],final=[],stats=[];
 const modules=["RleEdgePath","RleEdgeEndpoints"];
 const write=(m,s)=>fs.writeFileSync(path.join(outdir,m+".lean"),s);
 for(const [fi,family] of ["First","Second"].entries()){
  const section=roots.split("namespace "+family+"\n")[1].split("\nend "+family)[0];
  const original=new Map([...section.matchAll(/def (ckpt\d+) : RleFullState := ([\s\S]*?⟩)/g)].map(m=>[m[1],{literal:m[2],state:parseState(m[2])}]));
  const meta=counts.machines[fi],states=[original.get("ckpt0").state],costs=[];
  let state=states[0],total=0n,batches=0;
  // Check all original coarse endpoints and the independent exact costs.
  for(const ch of meta.chunkBounds){
   let subtotal=0n;
   if(stable(state)!==stable(original.get(ch.from).state))throw Error("checkpoint start "+ch.from);
   for(let i=0;i<ch.batches*25&&!state.halted;i++){
    const c=rleStepBound(state);
    state=rleStep(state);states.push(state);costs.push(c);subtotal+=c;
   }
   batches+=ch.batches;total+=subtotal;
   if(subtotal!==BigInt(ch.bound))throw Error("cost mismatch "+ch.from);
   if(ch.to&&stable(state)!==stable(original.get(ch.to).state))throw Error("checkpoint end "+ch.to);
  }
  if(!state.halted||total!==BigInt(meta.rleTransitionCostCandidate)||
     total+1n!==BigInt(meta.successfulPrimitiveStepCandidate)||
     total+2n!==BigInt(meta.includingHaltAttemptCandidate))throw Error("total or terminal mismatch");
  endpoints.push("namespace "+family);
  const blocks=[],endNames=["ckpt0"];
  endpoints.push("def ckpt0 : RleFullState := "+original.get("ckpt0").literal);
  for(let start=0;start<costs.length;start+=chunkSize){
   const end=Math.min(start+chunkSize,costs.length),idx=blocks.length;
   const en="endpoint_"+end;
   endpoints.push("def "+en+" : RleFullState := "+literal(states[end]));
   const mod="RleEdge"+family+String(idx).padStart(3,"0"),ns="Shard"+idx;
   const {defs,encoded}=listsFor(states.slice(start+1,end));
   const local=["import RleEdgeEndpoints\n"+open,"namespace "+family+"."+ns,...defs];
   const names=[endNames.at(-1)];
   for(let j=start+1;j<end;j++){
    names.push("state_"+j);
    local.push("private def state_"+j+" : RleFullState := "+encoded[j-start-1]);
   }
   names.push(en);
   let sum=0n,edges=[];
   for(let j=start;j<end;j++){
    const e="edge_"+j;edges.push(e);sum+=costs[j];
    local.push("private theorem "+e+" : CountPath "+names[j-start]+" "+names[j-start+1]+" "+costs[j]+" := .one rfl rfl rfl");
   }
   local.push("theorem certificate : CountPath "+names[0]+" "+en+" "+sum+" := "+balanced(edges));
   local.push("end "+family+"."+ns,close);
   write(mod,local.join("\n")+"\n");imports.push(mod);modules.push(mod);
   blocks.push({name:ns+".certificate",cost:sum});endNames.push(en);
  }
  endpoints.push("end "+family);
  final.push("namespace "+family,
   "theorem whole_path : CountPath ckpt0 "+endNames.at(-1)+" "+total+" := "+balanced(blocks.map(b=>b.name)),
   "theorem counted_reach_0 : StateHaltsAt "+family+".target_tm ckpt0 "+total+" := whole_path.halt rfl",
   section.slice(section.indexOf("theorem halts_exact")).trimEnd(),
   "end "+family);
  stats.push({family,edges:costs.length,shards:blocks.length,batches,successful:String(total+1n),score:String(total+2n)});
 }
 endpoints.push(close);
 write("RleEdgeEndpoints",endpoints.join("\n")+"\n");
 write("RleCountedRoots",imports.map(m=>"import "+m).join("\n")+"\n"+open+final.join("\n")+"\n"+close);
 modules.push("RleCountedRoots");
 fs.writeFileSync(path.join(outdir,"edge-modules.txt"),modules.join("\n")+"\n");
 fs.writeFileSync(path.join(outdir,"edge-stats.json"),JSON.stringify(stats,null,2)+"\n");
 return stats;
}
module.exports={generate};
if(require.main===module){
 const out=process.argv[2];if(!out)throw Error("usage: generate_edge_roots.cjs OUTDIR [chunkSize]");
 fs.mkdirSync(out,{recursive:true});
 const other="../agent17-f289-exact-cost/";
 fs.copyFileSync(path.join(__dirname,"RleEdgePath.lean"),path.join(out,"RleEdgePath.lean"));
 console.log(JSON.stringify(generate(read(other+"RleCountedRoots.lean"),read("../agent42-cryptids-upstream-191-overlap/simulate_f289_rle.js"),read(other+"replay_exact_cost.js"),JSON.parse(read(other+"exact-candidate-counts.json")),out,Number(process.argv[3]??500))));
}
