'use strict';
// Six-hole Raw11 discovery; no proof claim. Each complete retained tree has
// its exact open-leaf roster. Previously scanned 131,133 are excluded.
const fs = require('node:fs');
const path = require('node:path');
const {search} = require('../agent47-raw11-adapter/generate-raw11-extra.cjs');
const {solve} = require('./q0-open-automata.cjs');
const route = require('../agent47-raw11-adapter/raw11-route.json');
const shard = Number(process.argv[2] || 0);
const shards = Number(process.argv[3] || 8);
const cap = Number(process.argv[4] || 400000);
if (!Number.isSafeInteger(shard) || !Number.isSafeInteger(shards) || shards<1 || shard<0 || shard>=shards ||
    !Number.isSafeInteger(cap) || cap<1) throw Error('invalid scan parameters');
const ids=route.extra.map((table,id)=>({table,id})).filter(({table,id})=>
  (table.match(/---/g)||[]).length===6 && id!==131 && id!==133);
const params=[
  ['run',6,3,3],['lag3',3,2,2],['blk3',3,3,3],['lag2',4,1,1],
  ['blk5',2,1,2],['lag4',3,2,2],['run',6,2,4],['ngram',12,2,2],
  ['lag2',6,3,2],['alt',6,3,3],['blk4',3,2,2],['lag3',6,2,2]
];
function extended(table){
  for(const [kind,k,c,d] of params) for(const mirror of [false,true]){
    const cert=solve(table,k,kind,mirror,60000,c,d);
    if(cert) return cert;
  }
  return null;
}
const out=path.join(__dirname,'six-hole-scan-'+shard+'.json');
const rows=[];
for(const {id,table} of ids.filter((_,i)=>i%shards===shard)){
  const t=Date.now(),r=search(table,{cap,retain:true});
  const certs=[],unresolved=[];
  if(r.tree) for(const [i,leaf] of r.opens.entries()){
    const cert=extended(leaf.replaceAll('_',''));
    if(cert) certs.push({i,cert}); else unresolved.push(i);
  }
  const row={id,table,nodes:r.n,bound:r.bound,complete:!!r.tree,stats:r.stats,
    opens:r.opens,certs,unresolved,ms:Date.now()-t};
  rows.push(row);
  fs.writeFileSync(out,JSON.stringify({shard,shards,cap,rows}));
  console.log(JSON.stringify({id,nodes:row.nodes,bound:row.bound,complete:row.complete,
    opens:row.opens.length,certs:certs.length,unresolved:unresolved.map(i=>r.opens[i]),ms:row.ms}));
}
