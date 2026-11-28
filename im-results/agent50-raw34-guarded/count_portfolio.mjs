#!/usr/bin/env node
/**
 * Source-independent exact BigInt audit of the Raw34 guarded-E family
 * against the previously source-accepted 3,087-cylinder portfolio and
 * Agent40's nine all-symbol closed-control families.
 *
 * The *mathematical* nonhalting proof must separately be source-checked:
 * BB6.Agent50Raw34GuardedE.never. This script asserts finite arithmetic;
 * it does not certify Lean axioms or a complete Raw34 Cover.
 *
 * Run: node im-results/agent50-raw34-guarded/count_portfolio.mjs
 */
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {dirname,join} from 'node:path';
import {fileURLToPath} from 'node:url';
const dir=dirname(fileURLToPath(import.meta.url));
const base=join(dir,'../agent50-raw34-firsthole');
const d2=JSON.parse(readFileSync(join(base,'depth2-candidate-witnesses.json'),'utf8'));
const d3=JSON.parse(readFileSync(join(base,'depth3-candidate-witnesses.json'),'utf8'));
assert.equal(d2.second_level.length,74);
assert.equal(d3.witnesses.length,1206);
const slots=[7,5,3,1,8,9,10,11]; // D1 C1 B1 A1 E0 E1 F0 F1
const vals=['HALT'];
for(const w of '01')for(const dir of 'LR')
  for(const q of 'ABCDEF')vals.push(w+dir+q);
assert.equal(vals.length,25);
const index=new Map(vals.map((v,i)=>[v,i]));
const ALL=(1<<25)-1;
function bit(v){assert(index.has(v),v);return 1<<index.get(v)}
function moves(states){
  const a=[];
  for(const w of '01')for(const d of 'LR')
    for(const s of states)a.push(w+d+s);
  return a;
}
function mask(values){return values.reduce((a,v)=>a|bit(v),0)}
function table(t){
  const str=t.replaceAll('_','');
  assert.equal(str.length,36,t);
  return slots.map(i=>{
    const v=str.slice(3*i,3*i+3);
    return v==='---'?ALL:bit(v);
  });
}
function given(...pairs){
  const x=Array(8).fill(ALL);
  for(const [i,v] of pairs)x[i]=bit(v);
  return x;
}
const accepted=[];
accepted.push(...'0LA 0LB 0LC 0RA 0RB 0RC 0RD 1LC 1RA 1RB 1RC'
  .split(' ').map(v=>given([0,v])));
accepted.push(...d2.second_level.map(x=>table(x.table)));
accepted.push(table('1RB---_1RC---_0RD1LC_1LC1RD_------_------'));
for(const c of moves('CD'))for(const d of moves('CD'))
  accepted.push(given([0,d],[1,c]));
accepted.push(...d3.witnesses.map(x=>table(x.table)));
for(const b of moves('BCD'))for(const c of moves('BCD'))
  for(const d of moves('BCD'))accepted.push(given([0,d],[1,c],[2,b]));
accepted.push(table('1RB1LD_1RC---_0RD0RA_1LC1RD_------_------'));
accepted.push(table('1RB---_1RC---_0RD0RE_1LC1RD_---1LD_------'));
accepted.push(table('1RB---_1RC---_0RD0LD_1LC0RE_1RD---_------'));
assert.equal(accepted.length,3087);

const graphSets=['CDE','CDF','CDEF','BCDE','BCDF','BCDEF','ABCD','ABCDE','ABCDF'];
const graph=graphSets.map(S=>{
  const allowed=mask(moves(S)),p=Array(8).fill(ALL);
  for(const [i,q] of [[0,'D'],[1,'C'],[2,'B'],[3,'A'],
                      [4,'E'],[5,'E'],[6,'F'],[7,'F']])
    if(S.includes(q))p[i]=allowed;
  return p;
});
const portfolio=[...new Map(accepted.concat(graph)
  .map(p=>[p.join(','),p])).values()];
assert.equal(portfolio.length,2885);

// This recursion counts an exact 25-way finite union *within* the
// restricted 8-slot product domain. A memo key retains the full
// surviving source-certificate mask set, avoiding overlap inflation.
function countUnionWithin(domains,patterns=portfolio){
  const choices=domains.map(m=>vals.map((v,i)=>i).filter(i=>m&(1<<i)));
  const masses=Array(9).fill(1n);
  for(let j=7;j>=0;j--)masses[j]=masses[j+1]*BigInt(choices[j].length);
  const memo=new Map();
  function coversEntireSuffix(id,at){
    for(let j=at;j<8;j++)
      if((patterns[id][j]&domains[j])!==domains[j])return false;
    return true;
  }
  function recur(ids,at){
    if(!ids.length)return 0n;
    if(at===8)return 1n;
    if(ids.some(i=>coversEntireSuffix(i,at)))return masses[at];
    const key=at+':'+ids.join(',');
    if(memo.has(key))return memo.get(key);
    let total=0n;
    for(const choice of choices[at])
      total+=recur(ids.filter(id=>patterns[id][at]&(1<<choice)),at+1);
    memo.set(key,total);
    return total;
  }
  return {covered:recur(patterns.map((_,i)=>i),0),
          universe:masses[0],memo_states:memo.size};
}
const FULL=Array(8).fill(ALL);
const acceptedMass=countUnionWithin(FULL,accepted).covered;
const portfolioMass=countUnionWithin(FULL,portfolio).covered;
assert.equal(acceptedMass,97539062500n);
assert.equal(portfolioMass,123226284000n);
const SAFE=mask([...moves('ACD'),'1RB']); // 13 actions
const GUARD_E=mask(['0LE','1LE']); // B1=>E, left, any write
const eDomain=[SAFE,SAFE,GUARD_E,SAFE,ALL,SAFE,ALL,ALL];
const eHalt=eDomain.slice();eHalt[4]=bit('HALT');
const E=countUnionWithin(eDomain),EH=countUnionWithin(eHalt);
assert.equal(E.universe,892531250n);
assert.equal(E.covered,878135700n);
assert.equal(E.universe-E.covered,14395550n);
assert.equal(EH.universe,35701250n);
assert.equal(EH.covered,32597500n);
assert.equal(EH.universe-EH.covered,3103750n);

// Label-symmetric F counterpart is an *exploratory* arithmetic diagnostic.
// It is NOT added to the certified claim until a true F-source proof exists.
const GUARD_F=mask(['0LF','1LF']);
const fDomain=[SAFE,SAFE,GUARD_F,SAFE,ALL,ALL,ALL,SAFE];
const FH=fDomain.slice();FH[6]=bit('HALT');
const F=countUnionWithin(fDomain),Fhalt=countUnionWithin(FH);
function str(x){return String(x)}
console.log(JSON.stringify({
 status:'exact finite arithmetic, source theorem separately requires Lean acceptance',
 raw34_size:str(25n**8n),
 accepted_prior_cylinders:accepted.length,
 accepted_previous_mass:str(acceptedMass),
 agent40_nine_graph_plus_previous:str(portfolioMass),
 guarded_E:{size:str(E.universe),
   inside_old_and_graph:str(E.covered),
   new_outside_old_and_graph:str(E.universe-E.covered),
   new_portfolio_total_if_source_accepted:str(portfolioMass+E.universe-E.covered),
   E0_is_HALT:{size:str(EH.universe),
     old_and_graph:str(EH.covered),
     new_nontrivial:str(EH.universe-EH.covered)}},
 guarded_F_exploratory_only:{size:str(F.universe),
   inside_old_and_graph:str(F.covered),
   new_outside_old_and_graph:str(F.universe-F.covered),
   F0_is_HALT:{size:str(Fhalt.universe),
     old_and_graph:str(Fhalt.covered),
     new_nontrivial:str(Fhalt.universe-Fhalt.covered)}},
 unique_portfolio_patterns:portfolio.length,
 E_memo_states:E.memo_states
},null,2));
