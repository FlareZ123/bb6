#!/usr/bin/env node
const fs=require('node:fs');const path=require('node:path');
const sourcePath=path.join(__dirname,'PairCarrySynchronizingSubsetDFA.json');
const outputPath=path.join(__dirname,'PairCarrySyncDFATransformationMonoid.json');
const d=JSON.parse(fs.readFileSync(sourcePath,'utf8')),T=d.minimized_transitions,N=T.length,key=f=>f.join(',');
const maps=[Array.from({length:N},(_,i)=>i)],representatives=[[]],ids=new Map([[key(maps[0]),0]]),transitions=[],levels=[1];
for(let h=0;h<maps.length;h++){const row=[];for(let a=0;a<9;a++){const next=maps[h].map(s=>T[s][a]),k=key(next);let id=ids.get(k);if(id===undefined){id=maps.length;ids.set(k,id);maps.push(next);representatives.push(representatives[h].concat(a));const depth=representatives[id].length;levels[depth]=(levels[depth]||0)+1;}row.push(id);}transitions.push(row);}
const rankDistribution={},powerStabilityDistribution={},exponent4Elements=[];
for(let i=0;i<maps.length;i++){const f=maps[i],rank=new Set(f).size;rankDistribution[rank]=(rankDistribution[rank]||0)+1;let p=Array.from({length:N},(_,j)=>j),stable=null;for(let k=1;k<=10;k++){const next=p.map(s=>f[s]);if(key(next)===key(p)){stable=k;break;}p=next;}if(stable===null)throw new Error('non-aperiodic element '+i);powerStabilityDistribution[stable]=(powerStabilityDistribution[stable]||0)+1;if(stable===4)exponent4Elements.push({id:i,representative:representatives[i]});}
const result={schema:'bb6-sync-dfa-transformation-monoid/v1',source:{path:sourcePath},state_count:N,alphabet:d.alphabet,monoid_size:maps.length,shortest_representatives_by_length:levels,rank_distribution:rankDistribution,power_stability_distribution:powerStabilityDistribution,aperiodic_exponent:Math.max(...Object.keys(powerStabilityDistribution).map(Number)),exponent4_elements:exponent4Elements,representatives,transformations:maps,transitions};
fs.writeFileSync(outputPath,JSON.stringify(result,null,2)+'\n');console.log(JSON.stringify({monoid_size:result.monoid_size,levels,rankDistribution,powerStabilityDistribution},null,2));
