#!/usr/bin/env node
/**
 * Exact physical-table arithmetic for ten Raw34 closed-control subfamilies. This is not a
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
// Overlap between already accepted certificate families is expected: 3,087
// source patterns contain 2,876 distinct literal patterns. The recursive
// union calculator handles both duplication and proper cylinder overlap.
assert.equal(new Set(old.map(JSON.stringify)).size,2876);


/*
 * Enumerate the nine *nontrivial* possible closed state subsets S containing
 * C and D. (CD/BCD are already included in prior source-proved certificates.
 * ABCDEF is included as the tautological no-HALT family, to avoid
 * treating obvious all-ordinary tables as still unclassified.)
 *
 * If A is in S, B must be in S (A0→B); if B is in S, C must be
 * in S (B0→C); C and D must occur together (C0→D and D0→C).
 * Each candidate S is a source-accepted nonhalting condition under the
 * generic Raw34GraphClosed.never_of_closed_control theorem once compiled.
 */
const families=[
  "CDE","CDF","CDEF","BCDE","BCDF","BCDEF",
  "ABCD","ABCDE","ABCDF","ABCDEF",
].map((S,i)=>({
  S,bit:1<<i,
  sourceSlots:["D1","C1","B1","A1","E0","E1","F0","F1"]
    .map((name,j)=>S.includes(name[0])?j:-1).filter(j=>j>=0),
}));
assert.equal(families.length,10);
const maskAll=(1<<families.length)-1;
const freeMemo=new Map(),mainMemo=new Map();

function nextMask(mask,at,action){
  if(mask===0)return 0;
  for(const f of families){
    if((mask&f.bit)!==0 && f.sourceSlots.includes(at) &&
       (action==="HALT"||!f.S.includes(action[2])))
      mask &= ~f.bit;
  }
  return mask;
}

function freeAfterOld(at,mask){
  if(!mask)return 0n;
  if(at===8)return 1n;
  const key=at+":"+mask;
  if(freeMemo.has(key))return freeMemo.get(key);
  let sum=0n;
  for(const action of alphabet)
    sum+=freeAfterOld(at+1,nextMask(mask,at,action));
  freeMemo.set(key,sum);
  return sum;
}

function countOutsideOld(ids,at,mask){
  if(!mask)return 0n;
  if(ids.some(id=>old[id].slice(at).every(x=>x===null)))return 0n;
  if(ids.length===0)return freeAfterOld(at,mask);
  assert(at<8,"fully-fixed false unmatched certificate");
  const key=at+":"+mask+":"+ids.join(",");
  if(mainMemo.has(key))return mainMemo.get(key);
  const wildcard=[],by=new Map();
  for(const id of ids){
    const v=old[id][at];
    if(v===null)wildcard.push(id);
    else{
      if(!by.has(v))by.set(v,[]);
      by.get(v).push(id);
    }
  }
  let sum=0n;
  for(const action of alphabet){
    const next=nextMask(mask,at,action);
    if(!next)continue;
    const filtered=[...wildcard,...(by.get(action)??[])].sort((a,b)=>a-b);
    sum+=countOutsideOld(filtered,at+1,next);
  }
  mainMemo.set(key,sum);
  return sum;
}

const fresh=countOutsideOld(old.map((_,i)=>i),0,maskAll);
assert.equal(fresh,37836625148n);
const older=97539062500n,total=older+fresh,unclassified=25n**8n-total;
assert.equal(total,135375687648n);
assert.equal(unclassified,17212202977n);

const branchD1="1RD";
const branchCandidates=old.map((_,i)=>i).filter(i=>
  old[i][0]===null||old[i][0]===branchD1);
const branchExtra=countOutsideOld(branchCandidates,1,nextMask(maskAll,0,branchD1));
const oldD1=3320312500n,oldAndTenD1=oldD1+branchExtra;
assert(oldAndTenD1<=25n**7n);
const newestAgent23D1=5993118083n;
assert(newestAgent23D1>=oldAndTenD1);
const agent23Increment=newestAgent23D1-oldAndTenD1;
const globalKnownWithAgent23=total+agent23Increment;
const globalOutsideWithAgent23=25n**8n-globalKnownWithAgent23;
assert(globalKnownWithAgent23>=total);

console.log(JSON.stringify({
  status:"Exact finite physical-cylinder arithmetic; generic Lean theorem and integration must be source-accepted independently",
  root:"1RB---_1RC---_0RD---_1LC---_------_------",
  earlierAcceptedCylinderPatterns:old.length,
  stateGraphFamilies:families.map(f=>f.S),
  additionalPhysicalCompletionsIfSoundlyIntegrated:String(fresh),
  earlierUnion:String(older),
  combinedNonhaltingMassIfAccepted:String(total),
  complementNotYetClassified:String(unclassified),
  memoizedSplitNodes:mainMemo.size,
  freeTailMaskNodes:freeMemo.size,
  D1_1RD_oldPlusTen:String(oldAndTenD1),
  D1_1RD_newestAgent23:String(newestAgent23D1),
  agent23IncrementBeyondOldTen:String(agent23Increment),
  knownWithAgent23:String(globalKnownWithAgent23),
  stillOutsideWithAgent23:String(globalOutsideWithAgent23),
},null,2));
