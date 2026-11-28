#!/usr/bin/env node
/**
 * Exact 25-ary physical-table union for the source theorem
 * BB6.Agent50Raw34Graph.never_of_finset.
 *
 * Raw34 fixed: A0=1RB, B0=1RC, C0=0RD, D0=1LC. At step 3
 * the machine is in D. A closed all-symbol set S must contain
 * C,D (D0->C,C0->D), and if A is included then B must be too.
 * The 12 possible sets are exhaustively enumerated below. For
 * an unknown slot whose source belongs to S, the 4|S| ordinary
 * moves targeting S are allowed; outside S, all 25 moves are free.
 *
 * This source theorem plus exact combinatorics certifies every
 * table counted by these patterns. No tape simulator and no
 * probabilistic sample is used. Source acceptance of the theorem
 * is a separate mandatory Lean CI gate.
 */
import { readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import assert from 'node:assert/strict';
const dir=dirname(fileURLToPath(import.meta.url));
const d2=JSON.parse(readFileSync(join(dir,'depth2-candidate-witnesses.json'),'utf8'));
const d3=JSON.parse(readFileSync(join(dir,'depth3-candidate-witnesses.json'),'utf8'));
assert.equal(d2.second_level.length,74);
assert.equal(d3.witnesses.length,1206);

const vals=['HALT'];
for(const w of '01')for(const d of 'LR')for(const s of 'ABCDEF')vals.push(w+d+s);
assert.equal(vals.length,25);
const index=new Map(vals.map((v,i)=>[v,i]));
const ALL=(1<<25)-1;
const bit=(v)=>{assert(index.has(v),v);return 1<<index.get(v)};
const slots=[7,5,3,1,8,9,10,11]; // D1 C1 B1 A1 E0 E1 F0 F1
function pattern(table){
  const s=table.replaceAll('_','');
  assert.equal(s.length,36,table);
  return slots.map(i=>{
    const v=s.slice(3*i,3*i+3);
    return v==='---'?ALL:bit(v);
  });
}
function constrained(...pairs) {
  const p=Array(8).fill(ALL);
  for(const [i,v] of pairs) p[i]=bit(v);
  return p;
}
function moves(states) {
  const a=[];
  for(const w of '01')for(const d of 'LR')for(const s of states)
    a.push(w+d+s);
  return a;
}

const old=[];
old.push(...'0LA 0LB 0LC 0RA 0RB 0RC 0RD 1LC 1RA 1RB 1RC'
  .split(' ').map(x=>constrained([0,x])));
old.push(...d2.second_level.map(x=>pattern(x.table)));
old.push(pattern('1RB---_1RC---_0RD1LC_1LC1RD_------_------'));
const cd=moves('CD'),bcd=moves('BCD');
for(const c of cd)for(const d of cd)
  old.push(constrained([0,d],[1,c]));
old.push(...d3.witnesses.map(x=>pattern(x.table)));
for(const b of bcd)for(const c of bcd)for(const d of bcd)
  old.push(constrained([0,d],[1,c],[2,b]));
old.push(pattern('1RB1LD_1RC---_0RD0RA_1LC1RD_------_------'));
old.push(pattern('1RB---_1RC---_0RD0RE_1LC1RD_---1LD_------'));
old.push(pattern('1RB---_1RC---_0RD0LD_1LC0RE_1RD---_------'));
assert.equal(old.length,2876);

const graph=[];
for(let mask=0;mask<16;mask++) {
  let S=['C','D'];
  for(let j=0;j<4;j++) if(mask&(1<<j))
    S.push(['A','B','E','F'][j]);
  if(S.includes('A')&&!S.includes('B'))continue;
  const allowed=moves(S).reduce((acc,v)=>acc|bit(v),0);
  const p=Array(8).fill(ALL);
  for(const [i,q] of [[0,'D'],[1,'C'],[2,'B'],[3,'A'],
                       [4,'E'],[5,'E'],[6,'F'],[7,'F']])
    if(S.includes(q))p[i]=allowed;
  graph.push({set:S.join(''),pattern:p});
}
assert.equal(graph.length,12);
assert.equal(graph.some(x=>x.set==='CDABEF'),true);

const powers=Array(9).fill(1n);
for(let i=7;i>=0;i--)powers[i]=powers[i+1]*25n;
function exactUnion(raw) {
  const pats=[...new Map(raw.map(p=>[p.join(','),p])).values()];
  const memo=new Map();
  const fullyFree=(id,at)=>{
    for(let j=at;j<8;j++)if(pats[id][j]!==ALL)return false;
    return true;
  };
  function count(ids,at){
    if(!ids.length)return 0n;
    if(at===8)return 1n;
    if(ids.some(id=>fullyFree(id,at)))return powers[at];
    const key=at+':'+ids.join(',');
    if(memo.has(key))return memo.get(key);
    const branches=Array.from({length:25},()=>[]);
    for(const id of ids) {
      const allowed=pats[id][at];
      for(let v=0;v<25;v++)
        if(allowed & (1<<v))branches[v].push(id);
    }
    let total=0n;
    for(const ids2 of branches)total+=count(ids2,at+1);
    memo.set(key,total);
    return total;
  }
  return {count:count(pats.map((_,i)=>i),0),
    uniquePatterns:pats.length,memoStates:memo.size};
}

const accepted=exactUnion(old);
assert.equal(accepted.count,97539062500n);
const newUnion=exactUnion(old.concat(graph.map(x=>x.pattern)));
const total=25n**8n;
const newMass=newUnion.count-accepted.count;
assert.equal(newUnion.count,135375687648n);
assert.equal(newMass,37836625148n);
assert.equal(total-newUnion.count,17212202977n);
console.log(JSON.stringify({
  baseline_accepted:accepted.count.toString(),
  graph_state_sets:graph.map(x=>x.set),
  exact_graph_plus_accepted:newUnion.count.toString(),
  additional_graph_safe_tables:newMass.toString(),
  unclassified_after_graph: (total-newUnion.count).toString(),
  full_raw34_tables:total.toString(),
  accepted_patterns:accepted.uniquePatterns,
  total_union_patterns:newUnion.uniquePatterns,
  memo_states:newUnion.memoStates,
  no_halt_instruction_tables:(24n**8n).toString()
},null,2));
