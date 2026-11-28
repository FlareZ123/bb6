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
const SAFE_B=mask([...moves('ACD'),'1RB']); // 13 actions into A,C,D or marked B
const SAFE_D=mask([...moves('ABC'),'0RD']); // 13 actions into A,B,C or zero-guard D
const SAFE_A=mask([...moves('BCD'),'0RA']); // 13 actions into B,C,D or initially-guarded A
const GUARD_E=mask(['0LE','1LE']);
const GUARD_F=mask(['0LF','1LF']);

// A/B/C-side predecessor-one guard: arbitrary E0 or F0 is never read.
const oneE=[SAFE_B,SAFE_B,GUARD_E,SAFE_B,ALL,SAFE_B,ALL,ALL];
const oneF=[SAFE_B,SAFE_B,GUARD_F,SAFE_B,ALL,ALL,ALL,SAFE_B];
const oneEHalt=oneE.slice();oneEHalt[4]=bit('HALT');
const oneFHalt=oneF.slice();oneFHalt[6]=bit('HALT');

// C0->D 0RD: D's left cell is unconditionally zero. D1 moves left
// into E/F scanning that zero, so E1/F1 can be HALT.
const zeroE=[GUARD_E,SAFE_D,SAFE_D,SAFE_D,SAFE_D,ALL,ALL,ALL];
const zeroF=[GUARD_F,SAFE_D,SAFE_D,SAFE_D,ALL,ALL,SAFE_D,ALL];
const zeroEHalt=zeroE.slice();zeroEHalt[5]=bit('HALT');
const zeroFHalt=zeroF.slice();zeroFHalt[7]=bit('HALT');

// Initial A starts on blank tape with its left predecessor 0.
// Every later entry into A via 0RA preserves the same predecessor,
// so A1 left into E/F always scans an E0/F0 zero.
const initialE=[SAFE_A,SAFE_A,SAFE_A,GUARD_E,SAFE_A,ALL,ALL,ALL];
const initialF=[SAFE_A,SAFE_A,SAFE_A,GUARD_F,ALL,ALL,SAFE_A,ALL];
const initialEHalt=initialE.slice();initialEHalt[5]=bit('HALT');
const initialFHalt=initialF.slice();initialFHalt[7]=bit('HALT');

// Exact two-sweep source classes (E1/F0/F1 and E0/E1/F1 free,
// respectively). Both have a 28n+44 period in the original zipper.
const twoE=table('1RB0LB_1RC1RE_0RD0LA_1LC0LD_0RA---_------');
const twoF=table('1RB0LB_1RC1RF_0RD0LA_1LC0LD_------_0RA---');

const families=[
 ['marked_B_E0',oneE,oneEHalt],
 ['marked_B_F0',oneF,oneFHalt],
 ['zero_D_E1',zeroE,zeroEHalt],
 ['zero_D_F1',zeroF,zeroFHalt],
 ['initial_A_E1',initialE,initialEHalt],
 ['initial_A_F1',initialF,initialFHalt],
 ['two_sweep_E',twoE,null],
 ['two_sweep_F',twoF,null]
];

// Pairwise disjoint by D1 or B1 action. Therefore summing each
// family's *new* contributions (outside the same prior portfolio)
// does not double count a physical completion.
for(let i=0;i<families.length;i++)
  for(let j=0;j<i;j++){
    const a=families[i][1],b=families[j][1];
    assert(a.some((m,k)=>(m&b[k])===0),
      `families ${families[i][0]} and ${families[j][0]} are not disjoint`);
  }
const detailed={};
let unionMass=portfolioMass;
for(const [name,domain,special] of families){
  const total=countUnionWithin(domain),nu=total.universe-total.covered;
  unionMass+=nu;
  detailed[name]={
    table_count:total.universe.toString(),
    previous_portfolio_intersection:total.covered.toString(),
    additional_outside_portfolio:nu.toString(),
    recursion_memo_states:total.memo_states
  };
  if(special){
    const ex=countUnionWithin(special);
    detailed[name].protected_instruction_equals_HALT={
      total:ex.universe.toString(),
      old_portfolio_overlap:ex.covered.toString(),
      new_nontrivial:(ex.universe-ex.covered).toString()
    };
  }
}
assert.equal(detailed.marked_B_E0.additional_outside_portfolio,'14395550');
assert.equal(detailed.marked_B_E0.protected_instruction_equals_HALT.new_nontrivial,'3103750');
assert.equal(detailed.zero_D_E1.additional_outside_portfolio,'52905450');
assert.equal(detailed.zero_D_F1.additional_outside_portfolio,'145517450');
assert.equal(detailed.initial_A_E1.additional_outside_portfolio,'3981250');
assert.equal(detailed.initial_A_F1.additional_outside_portfolio,'3981250');
assert.equal(detailed.initial_A_E1.protected_instruction_equals_HALT.new_nontrivial,'796250');
assert.equal(detailed.initial_A_F1.protected_instruction_equals_HALT.new_nontrivial,'796250');
assert.equal(detailed.two_sweep_E.additional_outside_portfolio,'3125');
assert.equal(detailed.two_sweep_F.additional_outside_portfolio,'3125');
console.log(JSON.stringify({
 status:'Exact BigInt finite arithmetic; new NeverHalts source claims require Lean acceptance',
 raw34_size:String(25n**8n),
 accepted_prior_cylinders:accepted.length,
 accepted_previous_mass:String(acceptedMass),
 agent40_nine_graph_plus_previous:String(portfolioMass),
 families:detailed,
 arithmetic_union_if_all_sources_accepted:String(unionMass),
 arithmetic_uncovered_within_raw34_if_all_sources_accepted:String(25n**8n-unionMass),
 unique_prior_portfolio_patterns:portfolio.length
},null,2));
