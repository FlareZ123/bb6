#!/usr/bin/env node
/**
 * Exact physical-table arithmetic for an additional Raw34 source-proved
 * nonhalting family with closed C,D,E control states. This is not a
 * substitute for Lean source acceptance of Raw34ClosedCDE.all_cde.
 *
 * Root: 1RB---_1RC---_0RD---_1LC---_------_------
 * Slots (in physical first-hole order): D1,C1,B1,A1,E0,E1,F0,F1
 * Each slot has 25 distinct total-machine actions (HALT included).
 * New source family: C1,D1,E0,E1 each have successor in C,D,E.
 * Other four slots remain true wildcards (HALT permitted).
 *
 * We compute the exact set difference with the union of all independently
 * proved earlier cylinders, including three polynomial growth parents.
 * The count recursion tests actual literal source patterns, memoizes
 * branch states and never samples executions or projects quotient states.
 */
import assert from "node:assert/strict";
import {readFileSync} from "node:fs";
import {dirname,join} from "node:path";
import {fileURLToPath} from "node:url";

const root=join(dirname(fileURLToPath(import.meta.url)),"../agent50-raw34-firsthole");
const depth2=JSON.parse(readFileSync(join(root,"depth2-candidate-witnesses.json"),"utf8")).second_level;
const depth3=JSON.parse(readFileSync(join(root,"depth3-candidate-witnesses.json"),"utf8")).witnesses;
assert.equal(depth2.length,74);
assert.equal(depth3.length,1206);

const alphabet=["HALT"];
for(const w of "01") for(const dir of "LR") for(const q of "ABCDEF") alphabet.push(w+dir+q);
assert.equal(alphabet.length,25);

const slots=[7,5,3,1,8,9,10,11]; // D1, C1, B1, A1, E0, E1, F0, F1
function parse(table) {
  const t=table.replaceAll("_","");
  assert.equal(t.length,36,table);
  const fixed=new Map([[0,"1RB"],[2,"1RC"],[4,"0RD"],[6,"1LC"]]);
  for(const [index,action] of fixed) assert.equal(t.slice(index*3,index*3+3),action,table);
  return slots.map(i=>{
    const x=t.slice(i*3,i*3+3);
    assert(x==="---"||alphabet.includes(x),"invalid physical action "+x);
    return x==="---"?null:x;
  });
}
const old=[];
const add=p=>old.push(p);
"0LA 0LB 0LC 0RA 0RB 0RC 0RD 1LC 1RA 1RB 1RC".split(" ").forEach(x=>add([x,null,null,null,null,null,null,null]));
depth2.forEach(x=>add(parse(x.table)));
add(parse("1RB---_1RC---_0RD1LC_1LC1RD_------_------"));
const cd=[];
for(const w of "01")for(const d of "LR")for(const q of "CD")cd.push(w+d+q);
for(const c1 of cd)for(const d1 of cd)add([d1,c1,null,null,null,null,null,null]);
depth3.forEach(x=>add(parse(x.table)));
const bcd=[];
for(const w of "01")for(const d of "LR")for(const q of "BCD")bcd.push(w+d+q);
for(const b1 of bcd)for(const c1 of bcd)for(const d1 of bcd)
  add([d1,c1,b1,null,null,null,null,null]);
for(const table of [
  "1RB1LD_1RC---_0RD0RA_1LC1RD_------_------",
  "1RB---_1RC---_0RD0RE_1LC1RD_---1LD_------",
  "1RB---_1RC---_0RD0LD_1LC0RE_1RD---_------",
])add(parse(table));
assert.equal(old.length,3087);
assert.equal(new Set(old.map(JSON.stringify)).size,old.length);

const cde=alphabet.filter(x=>x!=="HALT"&&"CDE".includes(x[2]));
assert.equal(cde.length,12);
const cdeSlots=new Set([0,1,4,5]);
const countPower=Array.from({length:9},(_,i)=>25n**BigInt(i));
const allowed=slots.map((_,i)=>cdeSlots.has(i)?cde:alphabet);
const suffixMass=Array.from({length:9},(_,i)=>
  allowed.slice(i).reduce((product,choices)=>product*BigInt(choices.length),1n));
assert.equal(suffixMass[0],12n**4n*25n**4n);
const allIds=old.map((_,i)=>i);

function unclassifiedUnderNewFamily(d1){
  const memo=new Map();
  function count(ids,at){
    if(ids.some(id=>old[id].slice(at).every(x=>x===null)))return 0n;
    if(ids.length===0)return suffixMass[at];
    assert(at<8,"fully fixed unmatched key");
    const key=at+":"+ids.join(",");
    if(memo.has(key))return memo.get(key);
    const wildcard=[],by=new Map();
    for(const id of ids){
      const action=old[id][at];
      if(action===null)wildcard.push(id);
      else {
        if(!by.has(action))by.set(action,[]);
        by.get(action).push(id);
      }
    }
    let sum=0n;
    for(const action of allowed[at]){
      const next=[...wildcard,...(by.get(action)??[])].sort((a,b)=>a-b);
      sum+=count(next,at+1);
    }
    memo.set(key,sum);
    return sum;
  }
  const stillLive=allIds.filter(id=>old[id][0]===null||old[id][0]===d1);
  return {D1:d1,newlyNonhalting:count(stillLive,1),memoStates:memo.size};
}

const cases=cde.map(unclassifiedUnderNewFamily);
const fresh=cases.reduce((s,e)=>s+e.newlyNonhalting,0n);
assert.equal(fresh,867187500n);
const previous=97539062500n;
const complete=25n**8n;
const covered=previous+fresh;
const unresolved=complete-covered;
assert.equal(covered,98406250000n);
assert.equal(unresolved,54181640625n);
assert.deepEqual(cases.map(x=>x.newlyNonhalting.toString()),
 ["0","93750000","117187500","0","0","84375000","0",
  "112500000","178125000","0","140625000","140625000"]);
console.log(JSON.stringify({
  status:"independent finite physical-table set difference; Lean source proof separate",
  root:"1RB---_1RC---_0RD---_1LC---_------_------",
  icalculator:"25-valued literal-cylinder recursion; no normalization",
  oldAcceptedPatterns:old.length,
  closedSuccessorSet:["C","D","E"],
  constrainedTransitions:["C1","D1","E0","E1"],
  familyTables:suffixMass[0].toString(),
  newlyCertifiedIfLeanAccepted:fresh.toString(),
  previousUnion:previous.toString(),
  updatedUnionIfLeanAccepted:covered.toString(),
  remainingOutsideTheseCertificatesIfAccepted:unresolved.toString(),
  cases:cases.map(({D1,newlyNonhalting,memoStates})=>({D1,newlyNonhalting:newlyNonhalting.toString(),memoStates}))
},null,2));
