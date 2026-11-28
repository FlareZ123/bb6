'use strict';
const {step,init}=require('./frontier_symbolic_graph.js');
const key=JSON.stringify, ser=x=>JSON.stringify(x,(_,v)=>typeof v==='bigint'?String(v):v);
let cache=new Map(),stats={detSteps:0,splitStates:0,loops:0,unknown:0,nonunit:0},terminalCounts=[];
function follow(s){let seen=new Set();for(;;){let k=key(s);if(seen.has(k)){stats.loops++;return 'loop'}seen.add(k);let e=step(s);stats.detSteps++;if(e.split)return k;if(e.halt)return 'halt';if(e.unknown){stats.unknown++;return 'unknown'}if(e.a%3n===0n){stats.nonunit++;return 'nonunit'}s=e.S}}
function targets(k){if(cache.has(k))return cache.get(k);let s=JSON.parse(k),out=[];for(let r=0n;r<3n;r++){let e=step(s,3n,r);if(e.split)throw Error('nested');if(e.halt)out.push('halt');else if(e.unknown){stats.unknown++;out.push('unknown')}else if(e.a%3n===0n){stats.nonunit++;out.push('nonunit')}else out.push(follow(e.S));}cache.set(k,out);stats.splitStates++;return out}
const fs=require('fs'),file=process.env.CHECKPOINT||'frontier-count.checkpoint.json';let layer=0,counts=new Map([[follow(init),1n]]);if(process.argv.includes('--resume')&&fs.existsSync(file)){let a=JSON.parse(fs.readFileSync(file,'utf8'));layer=a.layer;counts=new Map(a.counts.map(([k,v])=>[k,BigInt(v)]));terminalCounts=a.terminalCounts;console.error('resume',layer,counts.size)}
let max=Number(process.argv[2]||110),begin=Date.now(),ms=Number(process.argv[3]||120000);
for(;layer<max;layer++){
 let next=new Map(),halt=0n,other=0n;for(let [k,n] of counts){for(let t of targets(k)){if(t==='halt'){halt+=n;continue}if(t==='loop'||t==='unknown'||t==='nonunit'){other+=n;continue}next.set(t,(next.get(t)||0n)+n)}}
 let all=[...next.values()].reduce((a,b)=>a+b,0n);
 let prev=terminalCounts.length?BigInt(terminalCounts.at(-1).live):1n;
 if(all+halt+other!==3n*prev)throw Error('lost count');
 terminalCounts.push({layer:layer+1,halt:String(halt),other:String(other),live:String(all),states:next.size});counts=next;
 if((layer+1)%5===0||halt>0n)console.error(ser({layer:layer+1,halt,other,states:counts.size,cache:cache.size,stats,elapsed:Math.round((Date.now()-begin)/1000)}));
 if(Date.now()-begin>ms){layer++;break}
}
fs.writeFileSync(file,ser({layer,counts:[...counts],terminalCounts}));console.log(ser({layer,terminalCounts,stats}));
