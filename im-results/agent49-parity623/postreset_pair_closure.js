#!/usr/bin/env node
"use strict";
const fs=require("node:fs"),path=require("node:path");
const input=JSON.parse(fs.readFileSync(path.join(__dirname,"ResetPostStateDFA.json"),"utf8"));
function buildT(branch){const amin=branch==="L"?-2:-4,amax=branch==="L"?2:1,ac=amax-amin+1,n=9*ac*5,next=new Int32Array(n*9);next.fill(-1);for(let xp=0;xp<3;xp++)for(let yp=0;yp<3;yp++)for(let a=amin;a<=amax;a++)for(let b=-2;b<=2;b++){const s=(((xp*3+yp)*ac+(a-amin))*5+(b+2));for(let x=0;x<3;x++)for(let y=0;y<3;y++){let tx,ty;if(branch==="L"){tx=x-yp+a;ty=yp+b;}else{tx=-x-xp-yp+a;ty=xp+yp+b;}const an=Math.floor(tx/3),bn=Math.floor(ty/3);if(an<amin||an>amax||bn< -2||bn>2)continue;next[s*9+x*3+y]=(((x*3+y)*ac+(an-amin))*5+bn+2);}}return {amin,ac,n,next};}
const L=buildT("L"),R=buildT("R"),labels=input.post_reset_pair.output_labels;
function decode(T,s){const b=s%5-2,t=Math.floor(s/5),a=t%T.ac+T.amin,p=Math.floor(t/T.ac);return {state:s,previous_pair:[Math.floor(p/3),p%3],carry:[a,b]};}

const leanSource=fs.readFileSync(path.join(__dirname,"PostResetCarryPairInvariant.lean"),"utf8");
function leanTuples(name,nextName){
  const start=leanSource.indexOf("def "+name);
  const end=leanSource.indexOf("def "+nextName,start);
  if(start<0||end<0)throw Error("Lean tuple list not found: "+name);
  const block=leanSource.slice(start,end);
  return [...block.matchAll(/⟨\\s*(\\d+)\\s*,\\s*(\\d+)\\s*,\\s*(\\d+)\\s*,\\s*(\\d+)\\s*⟩/g)]
    .map(m=>m.slice(1).map(Number));
}
const leanAllStates=leanTuples("allStates","resetOutputLabels");
const leanSeedLabels=leanTuples("resetOutputLabels","allowedStates");
const expectedAllStates=[];
for(let px=0;px<3;px++)for(let py=0;py<3;py++)for(let la=0;la<2;la++)for(let ra=0;ra<4;ra++)expectedAllStates.push([px,py,la,ra]);
const expectedLeanSeeds=labels.map(label=>{
  const ld=decode(L,label.L_final_state),rd=decode(R,label.R_final_state);
  if(ld.previous_pair.join(",")!==rd.previous_pair.join(","))throw Error("seed previous-pair mismatch");
  const lk=ld.carry.join(",");
  const rk=rd.carry.join(",");
  const laCode={"-1,0":0,"0,0":1}[lk];
  const raCode={"-1,0":0,"-2,0":1,"-2,1":2,"-3,1":3}[rk];
  if(laCode===undefined||raCode===undefined)throw Error("seed carry outside Lean encoding");
  return [...ld.previous_pair,laCode,raCode];
});
const leanDataValidation={
  all_states_count:leanAllStates.length,
  all_states_complete:JSON.stringify(leanAllStates)===JSON.stringify(expectedAllStates),
  seed_labels_count:leanSeedLabels.length,
  seed_labels_unique:new Set(leanSeedLabels.map(x=>x.join(","))).size===leanSeedLabels.length,
  seed_labels_match_json_in_order:JSON.stringify(leanSeedLabels)===JSON.stringify(expectedLeanSeeds),
  missing_list_commas:/⟩\\s*\\n\\s*⟨/.test(leanSource)
};
if(!leanDataValidation.all_states_complete||
   leanDataValidation.seed_labels_count!==54||
   !leanDataValidation.seed_labels_unique||
   !leanDataValidation.seed_labels_match_json_in_order||
   leanDataValidation.missing_list_commas)throw Error("Lean/JSON finite-state data mismatch");
const keys=[],ids=new Map(),seedStateIds=[];for(const label of labels){const key=label.L_final_state+"|"+label.R_final_state;if(!ids.has(key)){ids.set(key,keys.length);keys.push(key);}seedStateIds.push(ids.get(key));}
const queue=keys.slice();for(let h=0;h<queue.length;h++){const [ls,rs]=queue[h].split("|").map(Number);for(let z=0;z<9;z++){const l=L.next[ls*9+z],r=R.next[rs*9+z];if(l<0||r<0)throw Error("invalid paired transition");const key=l+"|"+r;if(!ids.has(key)){ids.set(key,keys.length);keys.push(key);queue.push(key);}}}
const states=keys.map((key,id)=>{const [ls,rs]=key.split("|").map(Number),ld=decode(L,ls),rd=decode(R,rs);if(ld.previous_pair.join(",")!==rd.previous_pair.join(","))throw Error("previous-pair mismatch");return {id,L_state:ls,R_state:rs,previous_pair:ld.previous_pair,L_carry:ld.carry,R_carry:rd.carry,seed_label_indices:labels.map((v,i)=>v.L_final_state===ls&&v.R_final_state===rs?i:null).filter(v=>v!==null)};});
const transitions=states.map(s=>Array.from({length:9},(_,z)=>ids.get(L.next[s.L_state*9+z]+"|"+R.next[s.R_state*9+z])));
const perPrev={},profilesByX={},lp=new Set(),rp=new Set();let failures=0;for(const s of states){const x=s.previous_pair[0],y=s.previous_pair[1],k=x+","+y,p=s.L_carry.join(",")+"|"+s.R_carry.join(",");perPrev[k]=(perPrev[k]||0)+1;profilesByX[x]??=new Set();profilesByX[x].add(p);lp.add(s.L_state);rp.add(s.R_state);const rOK=[[-1,0],[-2,0],[-2,1],[-3,1]].some(v=>v[0]===s.R_carry[0]&&v[1]===s.R_carry[1]);const ok=s.L_carry[1]===0&&[-1,0].includes(s.L_carry[0])&&rOK&&!(x===0&&s.L_carry[0]===0&&s.R_carry[0]===-3&&s.R_carry[1]===1)&&!(x===2&&s.L_carry[0]===-1&&s.R_carry[0]===-1&&s.R_carry[1]===0);if(!ok)failures++;}
const result={description:"Least paired-state closure of the 54 common-reset output labels under every raw digit-pair symbol.",alphabet:{size:9,encoding:"symbol=3*x+y"},state_count:states.length,seed_count:labels.length,seed_state_ids:seedStateIds,states,transitions,invariant:{previous_pair:"(x,y) in {0,1,2}^2",left_carry:"(-1,0) or (0,0)",right_carry:"(-1,0), (-2,0), (-2,1), or (-3,1)",exclusions:["x=0, left carry (0,0), right carry (-3,1)","x=2, left carry (-1,0), right carry (-1,0)"],y_independent:true,states_per_previous_pair:perPrev,carry_profiles_by_previous_x:Object.fromEntries(Object.entries(profilesByX).map(([x,v])=>[x,[...v].sort()]))},validation:{L_projection_states:lp.size,R_projection_states:rp.size,previous_pair_mismatches:0,invariant_failures:failures,transitions_checked:states.length*9,invalid_transitions:0,outside_closure_transitions:0,closure_added_states:states.length-labels.length},lean_data_validation:leanDataValidation};
if(states.length!==66||failures!==0)throw Error("paired closure validation failed");
for(let i=0;i<states.length;i++)for(let z=0;z<9;z++)if(transitions[i][z]===undefined)throw Error("transition leaves closure");
fs.writeFileSync(path.join(__dirname,"PostResetCarryPairClosure.json"),JSON.stringify(result,null,2)+"\n");
console.log(JSON.stringify(result.validation,null,2));