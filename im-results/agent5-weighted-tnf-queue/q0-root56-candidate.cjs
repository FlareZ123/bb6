'use strict';
const fs = require('node:fs');
const path = require('node:path');
const {classify, bank, pairs, mitmPair} = require('./coarse-pair.cjs');
const {solve} = require('./q0-open-automata.cjs');
const moves = Array.from('ABCDEF').flatMap(q => Array.from('01').flatMap(w => Array.from('LR').map(d => w+d+q)));
const root = require('./q0-export/pilot-0-100-fuel-1000000.json').active[56];
if(root.table !== '1RB1RD_1RC---_0LA---_1LA0RE_------_------' || root.holes !== 6 || root.fresh !== 5) throw Error('root mismatch');
const target = '1RB1RD1RC0LC0LA1LB1LA0RE1LB1RF0RA---';
const traces = new Map([
 ['1RB1RD1RC0RA0LA1RE1LA0RE1LF0RC0LD---',12327],
 ['1RB1RD1RC1RA0LA1RE1LA0RE1LF0RC0LD---',12063],
]);
const params = new Map(fs.readFileSync(path.join(__dirname,'root56-far-params.tsv'),'utf8').trim().split('\n').map(l => {const [t,kind,k,m,cap,depth]=l.split(/\s+/);return [t,[+k,kind,m==='1',100000,+cap,+depth]];}));
const stats = {nodes:0,side:0,coarse:0,split:0,last:0,far:0,symbolic:0,maxHalt:0};
const far = {};
/** Totalize partial push edges to a fresh sink. */
function total(s){const n=s.push.length;return [...s.push.map(([x,y],i)=>[x,y].map((j,b)=>s.pop[j].some(([a,k])=>a===b&&k===i)?j:n)),[n,n]];}
/** Enumerate every ordinary transition at the first undefined slot. */
function visit(a,h){
  stats.nodes++;
  let c=classify(a,256);
  if(c.kind==='open'){
    for(const [l,r] of pairs) if(mitmPair(a,bank[l],bank[r])){stats.coarse++;return ['p',l,r];}
    c=classify(a,1500);
    if(c.kind==='open'){
      const t=a.join('');
      if(t===target){if(h!==1)throw Error('symbolic hole mismatch');stats.symbolic++;return ['c'];}
      if(traces.has(t)){c=classify(a,traces.get(t));if(c.kind!=='split'||c.n!==traces.get(t)||c.i!==11||h!==1)throw Error('long trace mismatch '+t);}
      else{
        if(!params.has(t))throw Error('unresolved '+t);
        const cert=solve(t,...params.get(t));
        if(!cert)throw Error('FAR failed '+t);
        const l=total(cert.left),r=total(cert.right);
        if(!mitmPair(a,l,r))throw Error('totalized MITM failed '+t);
        far[t]={left:l,right:r,rows:cert.rows.length};
        stats.far++;return ['d',l,r];
      }
    }
  }
  if(c.kind==='side'){stats.side++;return ['s',c.d,c.e,c.p,c.k];}
  if(c.kind!=='split')throw Error('unclassified');
  stats.maxHalt=Math.max(stats.maxHalt,c.n);
  if(h===1){stats.last++;return ['h',c.n,c.i,[]];}
  stats.split++;
  return ['h',c.n,c.i,moves.map(m=>{const b=a.slice();b[c.i]=m;return visit(b,h-1);})];
}
const tree=visit(root.table.replaceAll('_','').match(/.{3}/g),6);
const expected={nodes:360361,side:251964,coarse:8392,split:15015,last:84921,far:68,symbolic:1,maxHalt:12327};
for(const k of Object.keys(expected))if(stats[k]!==expected[k])throw Error('count mismatch '+k+' '+stats[k]);
if(Object.keys(far).length!==params.size||stats.nodes!==1+24*stats.split)throw Error('incomplete manifest');
const bound=stats.maxHalt+6;
if(process.argv[2])fs.writeFileSync(process.argv[2],JSON.stringify({rootId:56,table:root.table,bound,stats,far,tree}));
console.log(JSON.stringify({rootId:56,table:root.table,bound,stats}));
