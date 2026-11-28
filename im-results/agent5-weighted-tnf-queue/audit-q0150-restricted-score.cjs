#!/usr/bin/env node
"use strict";
/* Exact finite-table census and ordinary first-hole score for the 107-member
 * frozen q0-150 LAST-HOLE list. Source proofs of the 5 nonhalting leaves
 * and first-hole 102 finite leaves must be checked separately in Lean.
 * This code is an independent computational audit, NOT a formal proof of
 * the source search tree or a global BB(6) result.
 */
const assert=require("node:assert/strict");
const d=require("./q0-150-complete-frontier.json");
assert.equal(d.id,150);
assert.equal(d.stats.cap,0);
assert.equal(d.opens.length,107);
const choices=["---"];
for(const w of "01")for(const dir of "LR")for(const q of "ABCDEF")choices.push(w+dir+q);
assert.equal(choices.length,25);
const never=new Set([
 "1RB1LC_1RC1RB_0LA1LD_1LA0RE_1RD1RF_---1RD",
 "1RB1LC_1RC0RE_0LA1LD_1LA1RE_---0RF_1LC1RD",
 "1RB1LC_1RC0RE_0LA1LD_0RB1LC_---1RF_0LA1RB",
 "1RB1LC_1RC0RE_0LA1LD_0RB1LC_---1RF_0LD1RB",
 "1RB1LC_1RC0RE_0LA1LD_0RB1LC_---1RF_0RD1RB"
]);
const all=new Set(),halting=new Set(),finite=[];
let exceptional=0;
for(let i=0;i<d.opens.length;i++){
 const s=d.opens[i],t=s.replaceAll("_","").match(/.../g);
 assert.equal(t.length,12);
 const slot=t.indexOf("---");
 assert(slot>=0&&t.filter(x=>x==="---").length===1,s);
 for(const action of choices){
  const x=t.slice();x[slot]=action;
  const name=x.join("");
  assert(!all.has(name),`two distinct source leaves share complete machine at index ${i}`);
  all.add(name);
  if(action==="---")halting.add(name);
 }
 if(never.has(s)){exceptional++;continue;}
 const tape=new Set();
 let state=0,head=0,n=0;
 const cap=13007746;
 for(;n<=cap;n++){
  const tr=t[2*state+Number(tape.has(head))];
  if(tr==="---")break;
  assert(/^[01][LR][ABCDEF]$/.test(tr),s);
  if(tr[0]==="1")tape.add(head);else tape.delete(head);
  head+=tr[1]==="R"?1:-1;
  state=tr.charCodeAt(2)-65;
 }
 assert(n<=cap,`unresolved finite leaf ${i}: ${s}`);
 finite.push({i,firstHoleStep:n,haltingScore:n+1,table:s});
}
assert.equal(exceptional,5);
assert.equal(finite.length,102);
assert.equal(all.size,2675);
assert.equal(halting.size,107);
const max=Math.max(...finite.map(x=>x.haltingScore));
assert.equal(max,13007747);
const top=finite.filter(x=>x.haltingScore===max);
assert.equal(top.length,1);
console.log(JSON.stringify({
 source_run:d.source_run,source_root:d.table,
 enumerated_one_hole_leaves:d.opens.length,
 complete_machine_choices_per_leaf:25,
 distinct_complete_machines:all.size,
 distinct_halt_completion_machines:halting.size,
 currently_source_accepted_nonhalting_cylinders:exceptional,
 finite_first_hole_cylinders:finite.length,
 candidate_restricted_max_ordinary_steps:max,
 attaining_leaf:top[0],
 status:"finite computation plus separately certified local Covers; aggregate 107-leaf exact bound not yet kernel-accepted, and no canonical/global BB(6) implication"
},null,2));
