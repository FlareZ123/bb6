#!/usr/bin/env node
const fs=require('node:fs');const path=require('node:path');
const sourcePath=path.join(__dirname,'PairCarrySynchronizingSubsetDFA.json');
const outputPath=path.join(__dirname,'PairCarrySyncDFAMinimality.json');
const d=JSON.parse(fs.readFileSync(sourcePath,'utf8')),T=d.minimized_transitions,accept=new Set(d.accepting_states),n=T.length;
function witness(i,j){
 const start=i+','+j,parents=new Map([[start,null]]),symbols=new Map(),queue=[[i,j]];let head=0,found=null;
 while(head<queue.length){const [a,b]=queue[head++],k=a+','+b;if(accept.has(a)!==accept.has(b)){found=k;break;}for(let x=0;x<9;x++){const u=T[a][x],v=T[b][x],nk=u+','+v;if(!parents.has(nk)){parents.set(nk,k);symbols.set(nk,x);queue.push([u,v]);}}}
 if(found===null)return null;const word=[];let cur=found;while(cur!==start){word.push(symbols.get(cur));cur=parents.get(cur);}return word.reverse();
}
const distinguishers=[];for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){const word=witness(i,j);if(word===null)throw new Error('equivalent pair '+i+','+j);let a=i,b=j;for(const x of word){a=T[a][x];b=T[b][x];}if(accept.has(a)===accept.has(b))throw new Error('bad witness');distinguishers.push({i,j,word});}
const lengthDistribution={};for(const x of distinguishers)lengthDistribution[x.word.length]=(lengthDistribution[x.word.length]||0)+1;
const result={schema:'bb6-paired-carry-sync-dfa-minimality/v1',state_count:n,accepting_states:d.accepting_states,pair_count:distinguishers.length,max_shortest_distinguishing_word_length:Math.max(...distinguishers.map(x=>x.word.length)),length_distribution:lengthDistribution,distinguishers};
fs.writeFileSync(outputPath,JSON.stringify(result,null,2)+'\n');console.log(JSON.stringify({pair_count:result.pair_count,max_length:result.max_shortest_distinguishing_word_length,length_distribution:result.length_distribution},null,2));
