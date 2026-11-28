#!/usr/bin/env node
/** Finite physical-table partition by existing source-proven Raw34 cylinders.
 * Regenerate: node export.mjs --write. Audit: node export.mjs
 * This is NOT a Lean theorem or a proof of a whole Raw34 Cover.
 */
import assert from "node:assert/strict";
import {readFileSync,writeFileSync} from "node:fs";
import {resolve,dirname} from "node:path";
import {fileURLToPath} from "node:url";
const here=dirname(fileURLToPath(import.meta.url));
const upstream=resolve(here,"../agent50-raw34-firsthole");
const d2=JSON.parse(readFileSync(resolve(upstream,"depth2-candidate-witnesses.json"),"utf8"));
const d3=JSON.parse(readFileSync(resolve(upstream,"depth3-candidate-witnesses.json"),"utf8"));
assert.equal(d2.second_level.length,74);
assert.equal(d3.witnesses.length,1206);
const alphabet=["HALT"];
for(const w of "01")for(const d of "LR")for(const s of "ABCDEF")alphabet.push(w+d+s);
assert.equal(alphabet.length,25);
const ord=[7,5,3,1,8,9,10,11],names=["D1","C1","B1","A1","E0","E1","F0","F1"];
const base=["1RB","---","1RC","---","0RD","---","1LC","---","---","---","---","---"];
function parse(t){
 const flat=t.replaceAll("_","");
 assert.equal(flat.length,36,"Invalid partial table "+t);
 const tokens=Array.from({length:12},(_,j)=>flat.slice(j*3,j*3+3));
 for(const j of [0,2,4,6])assert.equal(tokens[j],base[j],"Parent fixed slot mismatch "+t);
 return ord.map(j=>{
  const v=tokens[j];
  assert(v==="---"||alphabet.includes(v),"Invalid move "+v);
  return v==="---"?null:v;
 });
}
const ps=[],add=(id,table)=>ps.push({id,table,p:parse(table)});
for(const m of "0LA 0LB 0LC 0RA 0RB 0RC 0RD 1LC 1RA 1RB 1RC".split(" "))
 add("eleven/"+m,"1RB---_1RC---_0RD---_1LC"+m+"_------_------");
d2.second_level.forEach((x,i)=>add("depth2/"+i,x.table));
add("unary","1RB---_1RC---_0RD1LC_1LC1RD_------_------");
const cd=alphabet.filter(x=>x!=="HALT"&&"CD".includes(x[2]));
for(const c of cd)for(const d of cd)
 add("CD/"+c+"/"+d,"1RB---_1RC---_0RD"+c+"_1LC"+d+"_------_------");
d3.witnesses.forEach((x,i)=>add("depth3/"+i,x.table));
const bcd=alphabet.filter(x=>x!=="HALT"&&"BCD".includes(x[2]));
for(const b of bcd)for(const c of bcd)for(const d of bcd)
 add("BCD/"+b+"/"+c+"/"+d,"1RB---_1RC"+b+"_0RD"+c+"_1LC"+d+"_------_------");
add("pump/A","1RB1LD_1RC---_0RD0RA_1LC1RD_------_------");
add("pump/E","1RB---_1RC---_0RD0RE_1LC1RD_---1LD_------");
add("alternating","1RB---_1RC---_0RD0LD_1LC0RE_1RD---_------");
assert.equal(ps.length,3087);
assert.equal(new Set(ps.map(x=>x.id)).size,ps.length);
const pow=n=>25n**BigInt(n);
function leaf(path,source){
 const cells=base.slice(),haltingSlots=[];
 for(let j=0;j<path.length;j++){
  if(path[j]==="HALT")haltingSlots.push(names[j]);
  else if(path[j]!==null)cells[ord[j]]=path[j];
 }
 const ans={
  decisions:path,
  projection:[0,1,2,3,4,5].map(i=>cells.slice(2*i,2*i+2).join("")).join("_"),
  mass:pow(8-path.filter(x=>x!==null).length).toString()
 };
 if(haltingSlots.length)ans.explicitHalts=haltingSlots;
 if(source!==undefined)ans.source=source;
 return ans;
}
const covered=[],open=[],stat={nodes:0,splits:0,skips:0};
function visit(ids,k,path){
 stat.nodes++;
 if(!ids.length){open.push(leaf(path));return;}
 const witness=ids.find(i=>ps[i].p.slice(k).every(v=>v===null));
 if(witness!==undefined){covered.push(leaf(path,ps[witness].id));return;}
 assert(k<8,"Missing terminal proof");
 const free=[],by=new Map();
 for(const i of ids){
  const v=ps[i].p[k];
  if(v===null)free.push(i);
  else{if(!by.has(v))by.set(v,[]);by.get(v).push(i);}
 }
 if(!by.size){stat.skips++;visit(ids,k+1,[...path,null]);return;}
 stat.splits++;
 for(const v of alphabet)
  visit([...free,...(by.get(v)||[])].sort((a,b)=>a-b),k+1,[...path,v]);
}
const ids=ps.map((_,i)=>i).filter(i=>ps[i].p[0]===null||ps[i].p[0]==="1RD");
assert.equal(ids.length,271);
visit(ids,1,["1RD"]);
const total=xs=>xs.reduce((a,x)=>a+BigInt(x.mass),0n);
assert.equal(total(covered),3320312500n);
assert.equal(total(open),2783203125n);
assert.equal(total(covered)+total(open),pow(7));
assert.equal(covered.length,124);
assert.equal(open.length,165);
assert.deepEqual(stat,{nodes:314,splits:12,skips:13});
function intersects(a,b){
 for(let i=0;i<8;i++){
  const x=a[i]??null,y=b[i]??null;
  if(x!==null&&y!==null&&x!==y)return false;
 }
 return true;
}
for(const l of covered){
 const p=ps.find(x=>x.id===l.source);
 assert(p&&p.p.every((v,i)=>v===null||l.decisions[i]===v),"Invalid source containment");
}
for(const l of open)for(const p of ps)
 assert(!intersects(l.decisions,p.p),"Uncovered leaf intersects accepted input proof");
const leaves=[...covered,...open];
for(let i=0;i<leaves.length;i++)for(let j=i+1;j<leaves.length;j++)
 assert(!intersects(leaves[i].decisions,leaves[j].decisions),"Two physical leaves overlap");
const out={
 parent:"1RB---_1RC---_0RD---_1LC---_------_------",
 branch:"D1=1RD",slotOrder:names,alphabet,
 sourceProofs:ps.length,branchRelevantProofs:ids.length,
 summary:{
  total:"6103515625",
  provedNeverHalting:total(covered).toString(),
  notCoveredByTheseProofs:total(open).toString(),
  closedLeaves:covered.length,openLeaves:open.length,
  nodes:stat.nodes,splits:stat.splits,skips:stat.skips
 },
 sourceMap:{
  eleven:"Raw34ElevenSideCycles.lean (CI 46085109098)",
  depth2:"Raw34Depth2SideCycles.lean / depth2-candidate-witnesses.json (CI 46085429345)",
  unary:"Raw34UnaryGrowth.lean (CI 46085752374)",
  CD:"Raw34ClosedComponent.lean (CI 46086179976)",
  depth3:"Raw34Depth3Shard00..11.lean / depth3-candidate-witnesses.json (CI 46086787386)",
  BCD:"Raw34ClosedBCD.lean (CI 46086997664)",
  pump:"Raw34TripleSweepGrowth.lean (CI 46087571719)",
  alternating:"Raw34AlternatingGrowth.lean (CI 46087707935)"
 },
 covered,open
};
const content=JSON.stringify(out,null,2)+"\n";
const outPath=resolve(here,"D1-1RD-proof-frontier.json");
if(process.argv.includes("--write"))writeFileSync(outPath,content);
else assert.equal(readFileSync(outPath,"utf8"),content,"Stale generated manifest");
console.log(JSON.stringify(out.summary));
