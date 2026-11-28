'use strict';
// Independent primitive-step blank-orbit audit of the *complete* q0-150
// first-hole frontier from accepted frozen scan+resume run 46031415066.
// This is a computational audit, not a Lean proof or a global BB(6) Cover.
const fs=require('node:fs');
const assert=require('node:assert/strict');
const input=process.argv[2];
if(!input)throw Error('usage: node audit-q0150-open.cjs /path/to/resumed/summary.json');
const frontier=JSON.parse(fs.readFileSync(input,'utf8'));
const root='1RB1LC_1RC---_0LA1LD_------_------_------';
assert.equal(frontier.id,150);
assert.equal(frontier.table,root);
assert.equal(frontier.stats.cap,0);
assert.equal(frontier.opens.length,frontier.stats.open);
assert.equal(frontier.opens.length,107);
const never=new Map([
 ['1RB1LC_1RC1RB_0LA1LD_1LA0RE_1RD1RF_---1RD','Raw11Q0Sweep150'],
 ['1RB1LC_1RC0RE_0LA1LD_1LA1RE_---0RF_1LC1RD','Raw11Q0Double150'],
 ['1RB1LC_1RC0RE_0LA1LD_0RB1LC_---1RF_0LA1RB','Raw11Q0Frame150Rules.M0'],
 ['1RB1LC_1RC0RE_0LA1LD_0RB1LC_---1RF_0LD1RB','Raw11Q0Frame150Rules.M1'],
 ['1RB1LC_1RC0RE_0LA1LD_0RB1LC_---1RF_0RD1RB','Raw11Q0Frame150Rules.M2']
]);
const last=new Map([
 ['1RB1LC_1RC1RF_0LA1LD_0LB0RE_0LC1RD_1RA---',13007746],
 ['1RB1LC_1RC1RF_0LA1LD_0LE0RB_1LA---_1RA0LA',1102620],
 ['1RB1LC_1RC1RF_0LA1LD_1LE0RB_0LA---_1RA0LA',1102608],
 ['1RB1LC_1RC1RF_0LA1LD_1LE0RB_0RA---_1RA0LA',1102620],
 ['1RB1LC_1RC1RF_0LA1LD_1LE0RB_0LB---_1RA0LA',2625198]
]);
function firstHole(table,bound) {
 const tr=table.replaceAll('_','').match(/.{3}/g);
 assert.equal(tr.length,12);
 assert.equal(tr.filter(x=>x==='---').length,1);
 const tape=new Set();
 let state=0,head=0;
 for(let n=0;n<=bound;n++){
  const slot=2*state+Number(tape.has(head));
  const m=tr[slot];
  if(m==='---')return {n,slot};
  if(!m)throw Error('invalid transition '+table+' '+slot);
  if(m[0]==='1')tape.add(head);
  else if(m[0]==='0')tape.delete(head);
  else throw Error('invalid write');
  head+=m[1]==='R'?1:m[1]==='L'?-1:(()=>{throw Error('invalid direction')})();
  state=m.charCodeAt(2)-65;
  assert(state>=0&&state<6);
 }
 return null;
}
const finite=[],excluded=[];
const budget=13007746;
for(let i=0;i<frontier.opens.length;i++){
 const table=frontier.opens[i];
 if(never.has(table)){excluded.push({index:i,table,source:never.get(table)});continue;}
 const result=firstHole(table,budget);
 assert(result,`unclassified first-hole orbit: ${i} ${table}`);
 if(last.has(table))assert.equal(result.n,last.get(table),`wrong long trace at ${i}`);
 finite.push({index:i,table,...result});
}
assert.equal(excluded.length,5);
assert.equal(finite.length,102);
assert.equal(last.size,5);
for(const table of last.keys())assert(finite.some(x=>x.table===table));
assert(finite.every(x=>x.n+6<=13007752));
const short=finite.filter(x=>x.n<=100000);
const long=finite.filter(x=>x.n>100000);
assert.equal(short.length,97);
assert.equal(long.length,5);
const out={root,source_run:46031415066,source_stats:frontier.stats,
  simulation:'exact ordinary six-state two-symbol blank tape; first unknown transition',
  weighted_candidate_bound:13007752,
  finite_count:finite.length,short_count:short.length,nonhalt_prior_source_count:excluded.length,
  first_hole_max:Math.max(...finite.map(x=>x.n)),
  long_finite:long,
  never:excluded,finite};
console.log(JSON.stringify(out,null,2));
