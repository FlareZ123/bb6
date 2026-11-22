#!/usr/bin/env node
// Generate the image-subset automaton and its minimal synchronizing-language DFA.
const fs = require('node:fs');
const path = require('node:path');
const sourcePath = path.join(__dirname, '../agent49-parity623/PostResetCarryPairClosure.json');
const outputPath = path.join(__dirname, 'PairCarrySynchronizingSubsetDFA.json');
const closure = JSON.parse(fs.readFileSync(sourcePath, 'utf8'));
const N = closure.state_count;
if (!Number.isInteger(N) || closure.transitions.length !== N) throw new Error('invalid source automaton');
for (const row of closure.transitions) if (!Array.isArray(row) || row.length !== 9 || row.some(x => !Number.isInteger(x) || x < 0 || x >= N)) throw new Error('invalid transition row');
const key = xs => xs.join(',');
const subsets = [Array.from({length:N}, (_,i)=>i)], representatives = [[]], ids = new Map([[key(subsets[0]),0]]), transitions = [], levels = [1];
for (let h=0; h<subsets.length; h++) {
  const row=[];
  for (let a=0; a<9; a++) {
    const next=[...new Set(subsets[h].map(s=>closure.transitions[s][a]))].sort((x,y)=>x-y), k=key(next);
    let id=ids.get(k);
    if (id===undefined) { id=subsets.length; ids.set(k,id); subsets.push(next); representatives.push(representatives[h].concat(a)); levels[representatives[id].length]=(levels[representatives[id].length]||0)+1; }
    row.push(id);
  }
  transitions.push(row);
}
let blocks=subsets.map(s=>s.length===1?1:0), iterations=0;
while (true) {
  iterations++; const sigToId=new Map(), nextBlocks=[];
  for (let s=0; s<subsets.length; s++) {
    const sig=String(blocks[s])+'|'+transitions[s].map(t=>blocks[t]).join(',');
    let id=sigToId.get(sig); if (id===undefined) { id=sigToId.size; sigToId.set(sig,id); }
    nextBlocks[s]=id;
  }
  if (nextBlocks.every((x,i)=>x===blocks[i])) break;
  blocks=nextBlocks;
}
const classMap=new Map();
for(let s=0;s<blocks.length;s++){if(!classMap.has(blocks[s]))classMap.set(blocks[s],[]);classMap.get(blocks[s]).push(s);}
const classes=[...classMap.entries()].sort((a,b)=>a[0]-b[0]).map(x=>x[1]);
const minimizedStateOfSubset=Array(subsets.length);
classes.forEach((members,id)=>members.forEach(s=>minimizedStateOfSubset[s]=id));
const minimizedTransitions=classes.map(members=>{
  const row=transitions[members[0]].map(t=>minimizedStateOfSubset[t]);
  for(const s of members) if(transitions[s].some((t,a)=>minimizedStateOfSubset[t]!==row[a])) throw new Error('quotient is not well-defined');
  return row;
});
const acceptingStates=classes.map((members,id)=>members.every(s=>subsets[s].length===1)?id:null).filter(x=>x!==null);
const imageSizeDistribution={}; for(const s of subsets) imageSizeDistribution[s.length]=(imageSizeDistribution[s.length]||0)+1;
const minReps=classes.map(members=>members.map(i=>representatives[i]).sort((a,b)=>a.length-b.length)[0]);
const acceptingMembers=classes[acceptingStates[0]];
const shortestLength=Math.min(...acceptingMembers.map(i=>representatives[i].length));
const result={
  schema:'bb6-paired-carry-synchronizing-subset-dfa/v1',
  source:{path:sourcePath}, base_state_count:N,
  alphabet:Array.from({length:9},(_,i)=>String(Math.floor(i/3))+String(i%3)),
  image_subset_state_count:subsets.length, image_subset_states:subsets, image_subset_transitions:transitions,
  shortest_representatives:representatives, image_subset_level_counts:levels, image_size_distribution:imageSizeDistribution,
  nonempty_word_max_image_size:Math.max(...subsets.slice(1).map(s=>s.length)), singleton_subset_count:subsets.filter(s=>s.length===1).length,
  minimized_dfa_state_count:classes.length, minimized_state_of_subset:minimizedStateOfSubset, minimized_class_members:classes,
  minimized_transitions:minimizedTransitions, minimized_state_representatives:minReps,
  initial_state:minimizedStateOfSubset[0], accepting_states:acceptingStates, minimization_iterations:iterations,
  shortest_synchronizing_word_length:shortestLength, shortest_synchronizing_word_examples:acceptingMembers.map(i=>representatives[i]).filter(w=>w.length===shortestLength)
};
fs.writeFileSync(outputPath,JSON.stringify(result,null,2)+'\n');
console.log(JSON.stringify({image_subset_state_count:result.image_subset_state_count,minimized_dfa_state_count:result.minimized_dfa_state_count,levels:result.image_subset_level_counts,image_size_distribution:result.image_size_distribution,accepting_states:result.accepting_states,shortest_sync_length:result.shortest_synchronizing_word_length},null,2));
