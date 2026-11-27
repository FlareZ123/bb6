#!/usr/bin/env node
'use strict';

/**
 * Intermediate, independently implemented six-relative-permutation table audit.
 * Mathematical soundness is proved for the equivalent finite predicate in
 * RootedLiveQuotient.lean; a source/roster transport proof is required before
 * treating this JS output as a BB(6) formal certificate.
 */
const fs = require('fs');
const path = require('path');
const root = path.resolve(__dirname, '../..');
const read = p => JSON.parse(fs.readFileSync(path.join(root, p), 'utf8'));
const q0 = read('im-results/agent5-weighted-tnf-queue/q0-export/pilot-0-100-fuel-1000000.json');
const raw11 = read('im-results/agent44-raw11-fresh-cut/fresh-frontier.json');
const parent = '1RB---_1RC---_0LA---_------_------_------';
const ABCDEF = 'ABCDEF';

function parse(t) {
  const rows = t.split('_');
  if (rows.length !== 6 || rows.some(x => x.length !== 6)) throw Error('invalid six-state table: ' + t);
  return rows.flatMap(x => [x.slice(0,3), x.slice(3)]).map(x => x === '---' ? null : x);
}
function roots(t) {
  const p = parse(t), reach = new Set([0]), todo = [0];
  while (todo.length) {
    const q = todo.shift();
    for (const b of [0,1]) {
      const v = p[2*q+b];
      if (!v) continue;
      const tar = ABCDEF.indexOf(v[2]);
      if (tar >= 0 && !reach.has(tar)) { reach.add(tar); todo.push(tar); }
    }
  }
  return [...reach].sort((a,b) => a-b);
}
function permuteTail() {
  const arr = [3,4,5];
  function* gen(xs, pref=[]) {
    if (!xs.length) { yield pref; return; }
    for (let i=0; i<xs.length; i++) yield* gen(xs.filter((_,j)=>i!==j), [...pref,xs[i]]);
  }
  return [...gen(arr)].map(a => [0,1,2,...a]);
}
const perms = permuteTail();
if (JSON.stringify(roots(parent)) !== '[0,1,2]' || perms.length !== 6)
  throw Error('wrong parent connected component or tail subgroup');

function relativeOverlap(pt,qt,g) {
  for (let s=0;s<6;s++) for (let b=0;b<2;b++) {
    const a=pt[2*s+b], c=qt[2*g[s]+b];
    if (!a || !c) continue;
    // Halting instructions would need an explicit source codec. The imported
    // first-D/q0 partial rosters are all live rows or undefined holes.
    const target = ABCDEF.indexOf(a[2]);
    if (target<0 || ABCDEF.indexOf(c[2])<0)
      throw Error('unknown instruction encoding; require explicit halt transport');
    if (a[0]!==c[0] || a[1]!==c[1] || g[target]!==ABCDEF.indexOf(c[2])) return false;
  }
  return true;
}
function anchoredConflict(pt,qt) {
  const anchored = new Set(roots(parent));
  for (const s of anchored) for (const b of [0,1]) {
    const a=pt[2*s+b], c=qt[2*s+b];
    if (!a || !c) continue;
    const ta=ABCDEF.indexOf(a[2]), tc=ABCDEF.indexOf(c[2]);
    if (ta<0 || tc<0) throw Error('unknown halt codec');
    if (a[0]!==c[0] || a[1]!==c[1] ||
        ((anchored.has(ta)||anchored.has(tc)) && ta!==tc)) return true;
  }
  return false;
}
const queue = [...q0.active.map(x=>x.table), ...q0.held.map(x=>x.table)];
const frontier = raw11.frontier.map(x => typeof x==='string'?x:x.table);
if (queue.length !== 157 || frontier.length !== 116) throw Error('unexpected source roster length');
const qrows = queue.map(parse), frows=frontier.map(parse);
if (!queue.every(t=>relativeOverlap(parse(parent),parse(t),perms[0])) ||
    !frontier.every(t=>relativeOverlap(parse(parent),parse(t),perms[0])))
  throw Error('source row does not extend parent');

const lines = qrows.map((p, index) => {
  const exact=[], direct=[], rootConflicts=[];
  for (let j=0;j<frows.length;j++) {
    const q=frows[j], all=perms.some(g=>relativeOverlap(p,q,g));
    const id=relativeOverlap(p,q,perms[0]), rc=anchoredConflict(p,q);
    if (all) exact.push(j);
    if (id) direct.push(j);
    if (rc) rootConflicts.push(j);
    if (id && !all) throw Error('literal overlap but no quotient overlap');
    if (rc && all) throw Error('rooted conflict but quotient overlap: q0='+index+' frontier='+j);
  }
  return {index,table:queue[index],direct,quotient:exact,rootConflictCount:rootConflicts.length};
});
const output = {
  description: 'Finite JSON table crosswalk only; no Lean source manifest transport yet',
  parent, anchoredNames:roots(parent).map(x=>ABCDEF[x]),
  permutations:perms.map(g=>g.map(x=>ABCDEF[x]).join('')),
  sourceCounts:{q0:queue.length,frontier:frontier.length},
  overlapCounts:{
    directPairs:lines.reduce((n,x)=>n+x.direct.length,0),
    quotientPairs:lines.reduce((n,x)=>n+x.quotient.length,0),
    noDirect:lines.filter(x=>x.direct.length===0).length,
    noQuotient:lines.filter(x=>x.quotient.length===0).length,
    newQuotientPairs:lines.reduce((n,x)=>n+x.quotient.filter(j=>!x.direct.includes(j)).length,0)
  },
  changedFromLiteral:lines.filter(x=>x.quotient.length!==x.direct.length),
  q0TailRows:lines.slice(136,157).map(x=>({index:x.index,direct:x.direct,quotient:x.quotient,rootConflictCount:x.rootConflictCount}))
};
if (process.argv.includes('--write')) {
  fs.writeFileSync(path.join(__dirname,'raw11-six-tail-audit.json'),JSON.stringify(output,null,2)+'\n');
}
console.log(JSON.stringify(output,null,2));