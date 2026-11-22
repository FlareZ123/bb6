#!/usr/bin/env node
"use strict";
const fs=require("node:fs");
const path=require("node:path");
const here=__dirname;
const subsets=JSON.parse(fs.readFileSync(path.join(here,"PairCarrySynchronizingSubsetDFA.json"),"utf8"));
const pair=JSON.parse(fs.readFileSync(path.join(here,"../agent49-parity623/PostResetCarryPairClosure.json"),"utf8"));
const ss=subsets.image_subset_states, tr=subsets.image_subset_transitions, base=pair.states, n=ss.length;
let mismatches=0;
for(let i=0;i<n;i++) for(let a=0;a<9;a++){
  const expected=[...new Set(ss[i].map(q=>pair.transitions[q][a]))].sort((x,y)=>x-y);
  const actual=ss[tr[i][a]];
  if(expected.join(",")!==actual.join(",")) mismatches++;
}
if(mismatches) throw new Error("Subset transition table disagrees with 66-state closure");
const reverse=Array.from({length:n},()=>[]);
for(let u=0;u<n;u++) for(let a=0;a<9;a++) reverse[tr[u][a]].push(u);
const seen=new Uint8Array(n), finish=[];
function dfs1(v){seen[v]=1;for(const w of tr[v])if(!seen[w])dfs1(w);finish.push(v);}
for(let v=0;v<n;v++)if(!seen[v])dfs1(v);
seen.fill(0);
const components=[];
function dfs2(v,cc){seen[v]=1;cc.push(v);for(const w of reverse[v])if(!seen[w])dfs2(w,cc);}
for(let i=finish.length-1;i>=0;i--){const v=finish[i];if(!seen[v]){const cc=[];dfs2(v,cc);cc.sort((a,b)=>a-b);components.push(cc);}}
components.sort((a,b)=>a[0]-b[0]);
const compOf=Array(n).fill(-1);
components.forEach((cc,i)=>cc.forEach(v=>compOf[v]=i));
const self=Array.from({length:n},(_,i)=>tr[i].map((v,a)=>v===i?a:null).filter(x=>x!==null));
const recurrent=components.map(cc=>cc.length>1||cc.some(v=>self[v].length));
const bad=components.map((cc,i)=>({cc,i})).filter(({cc,i})=>recurrent[i]&&cc.some(v=>ss[v].length>1));
const sync=components.filter((cc,i)=>recurrent[i]&&cc.every(v=>ss[v].length===1));
const branchProjection=subset=>{
  const ps=subset.map(q=>base[q]);
  const L=[...new Set(ps.map(x=>x.L_state))].sort((a,b)=>a-b);
  const R=[...new Set(ps.map(x=>x.R_state))].sort((a,b)=>a-b);
  const prev=[...new Set(ps.map(x=>x.previous_pair.join(",")))];
  return {L_state_ids:L,R_state_ids:R,L_count:L.length,R_count:R.length,previous_pair:prev.length===1?prev[0].split(",").map(Number):null,previous_pair_count:prev.length};
};
const badDetails=bad.map(({cc},idx)=>{
  const states=cc.map(id=>{
    const proj=branchProjection(ss[id]);
    const internal=tr[id].map((to,symbol)=>compOf[to]===compOf[id]?{symbol,x:Math.floor(symbol/3),y:symbol%3,to}:null).filter(Boolean);
    return {id,image_subset:ss[id],...proj,internal_transitions:internal};
  });
  const all=states.flatMap(x=>x.internal_transitions);
  const symbols=[...new Set(all.map(e=>e.symbol))].sort((a,b)=>a-b);
  const fixedX=states.every(x=>x.internal_transitions.length===3&&new Set(x.internal_transitions.map(e=>e.x)).size===1&&x.internal_transitions.map(e=>e.y).sort().join(",")==="0,1,2");
  const xPlusY2=symbols.join(",")==="2,4,6"&&states.every(x=>x.internal_transitions.length===3);
  const cycleLike=states.every(x=>x.internal_transitions.length===1);
  let cycle=null;
  if(cycleLike){
    const start=cc[0];let q=start,ids=[],word=[];
    do{ids.push(q);const e=tr[q].map((to,symbol)=>compOf[to]===compOf[q]?{to,symbol}:null).filter(Boolean)[0];word.push(e.symbol);q=e.to;}while(q!==start&&ids.length<=cc.length+1);
    cycle={state_ids:ids,symbols:word,symbol_pairs:word.map(s=>[Math.floor(s/3),s%3])};
  }
  let type="general-recurrent";
  if(cc.length===30&&fixedX)type="fixed-x-free-y";
  else if(cc.length===6&&xPlusY2)type="x-plus-y-equals-2";
  else if(cc.length===1&&self[cc[0]].length===1)type="fixed-symbol-loop";
  else if(cycleLike)type="periodic-cycle";
  const projectionHistogram={};
  for(const s of states){const k=s.L_count+"/"+s.R_count;projectionHistogram[k]=(projectionHistogram[k]||0)+1;}
  return {label:"B"+(idx+1),type,state_ids:cc,subset_size_set:[...new Set(states.map(x=>x.image_subset.length))].sort((a,b)=>a-b),projection_histogram:projectionHistogram,internal_symbol_ids:symbols,internal_symbol_pairs:symbols.map(s=>[Math.floor(s/3),s%3]),cycle,states};
});
const badIds=new Set(badDetails.flatMap(x=>x.state_ids));
const transient=ss.map((s,i)=>s.length>1&&!badIds.has(i)?i:null).filter(x=>x!==null);
const singleton=ss.map((s,i)=>s.length===1?i:null).filter(x=>x!==null);
const componentHist={};for(const cc of components)componentHist[cc.length]=(componentHist[cc.length]||0)+1;
const dag=components.map(()=>new Set());
for(let u=0;u<n;u++)for(let a=0;a<9;a++){const v=tr[u][a];if(compOf[u]!==compOf[v])dag[compOf[u]].add(compOf[v]);}
const memo=new Map(),choice=new Map();
function longest(i){if(recurrent[i])return 0;if(memo.has(i))return memo.get(i);let best=-1,bestJ=null;for(const j of dag[i]){const z=1+longest(j);if(z>best){best=z;bestJ=j;}}memo.set(i,best);choice.set(i,bestJ);return best;}
let q=compOf[subsets.initial_state],statePath=[subsets.initial_state],symbolPath=[];
while(!recurrent[q]){
  const j=choice.get(q);if(j===undefined)throw new Error("transient component has no successor");
  let edge=null;
  outer:for(const u of components[q])for(let a=0;a<9;a++)if(compOf[tr[u][a]]===j){edge={symbol:a,to:tr[u][a]};break outer;}
  symbolPath.push(edge.symbol);statePath.push(edge.to);q=j;
}
const certificate={
  schema:"bb6-paired-carry-nonsynchronizing-scc/v1",
  status:"exact finite automaton structural certificate; not an authentic-root invariant",
  source_artifacts:["im-results/agent27-623-root-scan/PairCarrySynchronizingSubsetDFA.json","im-results/agent49-parity623/PostResetCarryPairClosure.json"],
  alphabet:{size:9,encoding:"symbol=3*x+y with x,y in {0,1,2}"},
  automata:{base_pair_carry_states:pair.state_count,subset_states:n,initial_subset_state:subsets.initial_state,initial_image_size:ss[subsets.initial_state].length,nonempty_word_max_image_size:subsets.nonempty_word_max_image_size},
  transition_reconstruction:{checked:n*9,mismatches},
  scc_partition:{
    total_components:components.length,
    component_size_histogram:componentHist,
    singleton_image_states:singleton.length,
    singleton_image_scc_size:sync.length===1?sync[0].length:null,
    transient_nonsingleton_states:transient,
    recurrent_nonsingleton_components:badDetails.length,
    recurrent_nonsingleton_states:badIds.size,
    recurrent_nonsingleton_components_detail:badDetails
  },
  transient_bound:{
    max_transitions:longest(compOf[subsets.initial_state]),
    witness_state_ids:statePath,
    witness_symbol_ids:symbolPath,
    witness_symbol_pairs:symbolPath.map(s=>[Math.floor(s/3),s%3]),
    terminal_component_state_ids:components[q]
  },
  interpretation:[
    "A singleton image subset is exactly rank-one synchronization of the 66-state paired-carry machine.",
    "Any infinite path that never synchronizes must eventually remain inside one of the ten recurrent nonsingleton SCCs listed here.",
    "Two 30-state SCCs permit, at each state, exactly one x digit and all three y digits; the six-state SCC permits exactly (0,2),(1,1),(2,0).",
    "The remaining recurrent obstructions are three four-cycles, one two-cycle, and three fixed-symbol loops.",
    "This is an automaton-level reduction only. It does not prove that the authentic #623 S-window stream avoids these obstructions."
  ]
};
const badProjectionHistogram={};
for(const x of badDetails)for(const [k,v] of Object.entries(x.projection_histogram))badProjectionHistogram[k]=(badProjectionHistogram[k]||0)+v;
certificate.scc_partition.recurrent_nonsingleton_projection_histogram=badProjectionHistogram;
if(mismatches!==0||singleton.length!==66||sync.length!==1||sync[0].length!==66||transient.length!==62||badDetails.length!==10||badIds.size!==83||certificate.transient_bound.max_transitions!==4)throw new Error("Unexpected SCC partition");
fs.writeFileSync(path.join(here,"NonSynchronizingSCCs.json"),JSON.stringify(certificate,null,2)+"\n");
console.log(JSON.stringify({states:n,transitions_checked:n*9,mismatches,scc_count:components.length,component_size_histogram:componentHist,singleton_sync_states:singleton.length,transient_nonsingleton_states:transient.length,bad_recurrent_components:badDetails.length,bad_recurrent_states:badIds.size,projection_histogram:badProjectionHistogram,max_transient_steps:certificate.transient_bound.max_transitions},null,2));
