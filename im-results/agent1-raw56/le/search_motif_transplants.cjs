#!/usr/bin/env node
/* Exhaustive deterministic periodic-stack donor transfer over frozen Raw56 E1=0LE hard leaves.
   This is UNTRUSTED DISCOVERY. Every hit must be compiled by the unmodified
   Lean FastBiDFA checker to become a mathematically valid nonhalting proof.
   Usage: node search_motif_transplants.cjs /path/to/global-le.open [cap=15000]
*/
'use strict';
const fs=require('node:fs'),crypto=require('node:crypto'),zlib=require('node:zlib');
const path=require('node:path');
const here=__dirname;
const EXPECTED_OPEN_SHA='aba63f28439c707c3343fd4ff53f66717d5924b88b1aa8012947f6039e0da7ef';
const EXPECTED_INVENTORY_SHA='869a651cebab0b5eda351eb783438e7040237b3412747f3ac6265629b840da6f';
const openPath=process.argv[2],cap=+(process.argv[3]||15000);
if(!openPath||!Number.isInteger(cap)||cap<100)throw Error('usage: node search_motif_transplants.cjs GLOBAL.open [cap]');
const sha=b=>crypto.createHash('sha256').update(b).digest('hex');
const original=fs.readFileSync(openPath);
if(sha(original)!==EXPECTED_OPEN_SHA)throw Error('wrong global canonical open-list SHA256');
const rows=original.toString('utf8').trimEnd().split('\n');
if(rows.length!==26493)throw Error('wrong canonical roster size');
const buf=zlib.gunzipSync(Buffer.from(fs.readFileSync(path.join(here,'inventory-79.json.gz.b64'),'utf8'),'base64'));
if(sha(buf)!==EXPECTED_INVENTORY_SHA)throw Error('wrong candidate inventory SHA256');
const inv=JSON.parse(buf);
const donors=JSON.parse(fs.readFileSync(path.join(here,'motif_spec.json'),'utf8'));
const {solve}=require('./motif_replay.cjs');
const pairs=[];const seen=new Set();
for(const row of donors){
  const key=JSON.stringify(row.params);
  if(seen.has(key))continue;
  seen.add(key);pairs.push({donor:row.id,params:row.params});
}
const known=new Set(donors.map(r=>r.id));
const targets=inv.remaining.filter(i=>!known.has(i));
const hits=[];const failures=[];
for(const id of targets){
  if(id<0||id>=rows.length)throw Error('bad hard-leaf id '+id);
  let matched=false,mostStates=0;
  for(const donor of pairs){
    const x=solve(rows[id],...donor.params,cap);
    mostStates=Math.max(x.states||0,mostStates);
    if(x.status!=='ok')continue;
    hits.push({
      id,table:rows[id],donor:donor.donor,params:donor.params,
      states:x.states,edges:x.edges,method:'untrusted_candidate_fixed_point'
    });
    matched=true;
    break;
  }
  if(!matched)failures.push({id,maxExplored:mostStates});
}
process.stdout.write(JSON.stringify({
  source_open_sha256:EXPECTED_OPEN_SHA,source_inventory_sha256:EXPECTED_INVENTORY_SHA,
  donor_param_pairs:pairs.length,hard:inv.remaining.length,
  preknown:known.size,attempted:targets.length,
  cap,found:hits.length,hits,remaining:failures
},null,2)+'\n');
