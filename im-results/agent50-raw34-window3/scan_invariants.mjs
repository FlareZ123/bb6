#!/usr/bin/env node
/**
 * Raw34 symbolic radius-one tape-window certificate enumerator.
 *
 * We enumerate finite, inductively closed invariants over each state
 * q in {A,B,C,D,E,F}, and the triple of actual tape values (left,
 * scanned, right). 14 local predicates are tested. Source A000 is
 * required to satisfy the invariant. For each assigned source slot
 * (q,b), every allowed action must take EVERY satisfying triple and
 * BOTH possible fresh off-window symbols into the destination
 * invariant. A source slot unreachable by the invariant permits
 * all 25 actions, HALT included. Four fixed Raw34 source actions
 * must belong to their allowed sets.
 *
 * This is *sound for every original infinite tape and all steps*:
 * any concrete move uses one of the two modeled far symbols.
 * A standalone Lean generic soundness theorem, not this JS script,
 * must be audited before describing new table counts as formally
 * proven. This JS enumerator supplies reproducible finite arithmetic.
 *
 * Source-combinatorial maximal patterns are obtained by eliminating
 * product-domain patterns included in another product-domain pattern.
 * A recursive 25-ary union with exact BigInt counts is then evaluated
 * against the accepted 3,087 Raw34 certificates plus the nine
 * Agent40 closed-control families, without overlap inflation.
 *
 * Run: node im-results/agent50-raw34-window3/scan_invariants.mjs
 */
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {dirname,join} from 'node:path';
import {fileURLToPath} from 'node:url';
const dir=dirname(fileURLToPath(import.meta.url));
const prev=join(dir,'../agent50-raw34-firsthole');
const d2=JSON.parse(readFileSync(join(prev,'depth2-candidate-witnesses.json'),'utf8'));
const d3=JSON.parse(readFileSync(join(prev,'depth3-candidate-witnesses.json'),'utf8'));
assert.equal(d2.second_level.length,74);
assert.equal(d3.witnesses.length,1206);

const names=['none','all','L0','L1','C0','C1','R0','R1',
 'C0orL1','C1orL0','C0orR1','C1orR0','L0orR1','L1orR0'];
const preds=[
 ()=>false,()=>true,(l,c,r)=>l===0,(l,c,r)=>l===1,
 (l,c,r)=>c===0,(l,c,r)=>c===1,(l,c,r)=>r===0,
 (l,c,r)=>r===1,(l,c,r)=>c===0||l===1,
 (l,c,r)=>c===1||l===0,(l,c,r)=>c===0||r===1,
 (l,c,r)=>c===1||r===0,(l,c,r)=>l===0||r===1,
 (l,c,r)=>l===1||r===0];
assert.equal(names.length,preds.length);
const N=names.length;
const truth=preds.map(f=>Array.from({length:8},(_,i)=>
 Number(f(i>>2,(i>>1)&1,i&1))));
const actions=['HALT'];
for(const w of '01')for(const d of 'LR')for(const q of 'ABCDEF')
 actions.push(w+d+q);
assert.equal(actions.length,25);
const index=new Map(actions.map((v,i)=>[v,i]));
const bit=v=>{assert(index.has(v),v);return 1<<index.get(v)};
const FULL=(1<<25)-1;
const slots=[7,5,3,1,8,9,10,11]; // D1 C1 B1 A1 E0 E1 F0 F1
const pop=n=>{let k=0;while(n){n&=n-1;k++;}return k};
function moves(states){
 const a=[];for(const w of '01')for(const d of 'LR')
   for(const q of states)a.push(w+d+q);return a;
}
const mask=a=>a.reduce((m,v)=>m|bit(v),0);
function pattern(table){
 const str=table.replaceAll('_','');
 assert.equal(str.length,36,table);
 return slots.map(i=>{
   const v=str.slice(i*3,i*3+3);
   return v==='---'?FULL:bit(v);
 });
}
function given(...pairs){
 const a=Array(8).fill(FULL);
 for(const [i,v] of pairs)a[i]=bit(v);
 return a;
}

const baseline=[];
baseline.push(...'0LA 0LB 0LC 0RA 0RB 0RC 0RD 1LC 1RA 1RB 1RC'
 .split(' ').map(x=>given([0,x])));
baseline.push(...d2.second_level.map(x=>pattern(x.table)));
baseline.push(pattern('1RB---_1RC---_0RD1LC_1LC1RD_------_------'));
for(const c of moves('CD'))for(const d of moves('CD'))
 baseline.push(given([0,d],[1,c]));
baseline.push(...d3.witnesses.map(x=>pattern(x.table)));
for(const b of moves('BCD'))for(const c of moves('BCD'))
 for(const d of moves('BCD'))
 baseline.push(given([0,d],[1,c],[2,b]));
baseline.push(...[
 '1RB1LD_1RC---_0RD0RA_1LC1RD_------_------',
 '1RB---_1RC---_0RD0RE_1LC1RD_---1LD_------',
 '1RB---_1RC---_0RD0LD_1LC0RE_1RD---_------'
].map(pattern));
assert.equal(baseline.length,3087);
const graphSets=['CDE','CDF','CDEF','BCDE','BCDF','BCDEF',
 'ABCD','ABCDE','ABCDF'];
for(const S of graphSets){
 const p=Array(8).fill(FULL),allowed=mask(moves(S));
 for(const [i,q] of [[0,'D'],[1,'C'],[2,'B'],[3,'A'],
                     [4,'E'],[5,'E'],[6,'F'],[7,'F']])
  if(S.includes(q))p[i]=allowed;
 baseline.push(p);
}
const old=[...new Map(baseline.map(p=>[p.join(','),p])).values()];
assert.equal(old.length,2885);

// For each source predicate, input scanned bit, destination predicate,
// and write/direction pair, decide a universal 2^3*2 local closure.
// wd = 2*write + (right ? 1 : 0). q is in the destination entry.
const safe=Array.from({length:N},()=>Array.from({length:2},
 ()=>Array.from({length:N},()=>Array(4).fill(false))));
for(let source=0;source<N;source++)
 for(let b=0;b<2;b++)for(let dest=0;dest<N;dest++)
 for(let wd=0;wd<4;wd++){
  let good=true;
  for(let window=0;window<8&&good;window++){
   if(!truth[source][window]||((window>>1)&1)!==b)continue;
   const l=window>>2,r=window&1,w=wd>>1,right=wd&1;
   for(let fresh=0;fresh<2;fresh++){
    const after=right?
      ((w<<2)|(r<<1)|fresh):
      ((fresh<<2)|(l<<1)|w);
    if(!truth[dest][after]){good=false;break}
   }
  }
  safe[source][b][dest][wd]=good;
 }
const tags=Array(6).fill(0);
const fixedRows=[[0,0,'1RB'],[1,0,'1RC'],[2,0,'0RD'],[3,0,'1LC']];
function allowed(q,b){
 let ans=0,j=1;
 for(let w=0;w<2;w++)for(let right=0;right<2;right++)
  for(let dest=0;dest<6;dest++){
   if(safe[tags[q]][b][tags[dest]][2*w+right])
    ans|=1<<j;
   j++;
  }
 if(!truth[tags[q]].some((v,i)=>v&&((i>>1)&1)===b))
  return FULL;
 return ans;
}
const collected=[];
function visit(target,at){
 if(at===6){
  const m=Array.from({length:6},(_,q)=>[allowed(q,0),allowed(q,1)]);
  if(fixedRows.some(([q,b,v])=>!(m[q][b]&bit(v))))return;
  const active0=truth[tags[target]].some((v,i)=>v&&((i>>1)&1)===0);
  const active1=truth[tags[target]].some((v,i)=>v&&((i>>1)&1)===1);
  if(active0===active1)return; // one target input symbol is excluded
  const name=String.fromCharCode(65+target);
  const incoming=mask(['0L'+name,'0R'+name,'1L'+name,'1R'+name]);
  let incomingPossible=false;
  for(let q=0;q<4;q++)for(let b=0;b<2;b++)
   if(truth[tags[q]].some((v,i)=>v&&((i>>1)&1)===b)
      &&(m[q][b]&incoming))incomingPossible=true;
  if(!incomingPossible)return; // graph-closure duplicate
  const p=[m[3][1],m[2][1],m[1][1],m[0][1],
           m[4][0],m[4][1],m[5][0],m[5][1]];
  const mass=p.reduce((acc,v)=>acc*BigInt(pop(v)),1n);
  if(mass>0n)collected.push({tags:tags.slice(),target,
     domain:p,mass});
  return;
 }
 if(at===target){
  for(let j=2;j<N;j++){tags[at]=j;visit(target,at+1)}
  return;
 }
 if(at===(target===4?5:4)){tags[at]=0;visit(target,at+1);return;}
 for(let j=1;j<N;j++){
  if(at===0&&!truth[j][0])continue;
  tags[at]=j;visit(target,at+1);
 }
}
visit(4,0);visit(5,0);

const distinct=[...new Map(collected.map(v=>
 [v.domain.join(','),v])).values()];
distinct.sort((a,b)=>a.mass>b.mass?-1:a.mass<b.mass?1:0);
const maximal=[];
for(const v of distinct){
 if(!maximal.some(u=>v.domain.every((m,i)=>(m & ~u.domain[i])===0)))
  maximal.push(v);
}
assert.equal(distinct.length,712);
assert.equal(maximal.length,160);

// Memoized union of overlapping 25-ary product masks. Exact BigInt;
// no floats, heuristic extrapolations, or Monte Carlo measures.
function exactUnion(patterns){
 const raw=[...new Map(patterns.map(p=>[p.join(','),p])).values()];
 const memo=new Map(),powers=Array(9).fill(1n);
 for(let i=7;i>=0;i--)powers[i]=25n*powers[i+1];
 const complete=(id,i)=>{
  for(let j=i;j<8;j++)if(raw[id][j]!==FULL)return false;
  return true;
 };
 function count(ids,i){
  if(!ids.length)return 0n;
  if(i===8)return 1n;
  if(ids.some(id=>complete(id,i)))return powers[i];
  const key=i+':'+ids.join(',');
  if(memo.has(key))return memo.get(key);
  let n=0n;
  for(let v=0;v<25;v++){
   const branch=ids.filter(id=>raw[id][i]&(1<<v));
   n+=count(branch,i+1);
  }
  memo.set(key,n);
  return n;
 }
 const covered=count(raw.map((_,i)=>i),0);
 return {covered,pattern_count:raw.length,memo_states:memo.size};
}
const oldUnion=exactUnion(old);
assert.equal(oldUnion.covered,123226284000n);
const combined=exactUnion(old.concat(maximal.map(x=>x.domain)));
const increment=combined.covered-oldUnion.covered;
assert(increment>=0n&&combined.covered<=25n**8n);
console.log(JSON.stringify({
 status:'finite arithmetic; generic local-window soundness theorem must be accepted by Lean before source-backed proof claim',
 raw34_size:String(25n**8n),
 predicate_templates:names,
 enumerated_distinct:distinct.length,
 maximal_patterns:maximal.length,
 old_source_plus_graph:String(oldUnion.covered),
 candidate_local_window_union:String(combined.covered),
 new_outside_old:String(increment),
 remaining_outside_local_window:String(25n**8n-combined.covered),
 bdd_memo_states:combined.memo_states,
 sample_maximal:maximal.slice(0,8).map(x=>({
  target:'ABCDEF'[x.target],tags:x.tags.map(i=>names[i]),
  mass:String(x.mass),domain:x.domain
 }))
},null,2));
