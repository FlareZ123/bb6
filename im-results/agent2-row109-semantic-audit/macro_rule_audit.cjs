// PINNED REPLAY SOURCES: 6aeb2384173cf4c93a9a7c7f418bb9b7b1839b39
const definition="tm = 1RB0LE_0RC---_1RD0LA_1RE0RF_1LC1RD_1RE1RA\n\n[metastates]\nLeft   < <E00\nRightC c> 10C>\nRightE e> 11E>\nRightEOnly E> E>\nRightD D> D>\nRightA a> 01A>\nRightB B> B>\nRightF F> F>\nLeftA  <a <A01\nLeftC  <C <C\n\n[blocks]\nL = ^\nX(exp) = 1\nD0 = 1100\nS0 = 1110\nD1 = 1111\n\nK = 10\nJ = 01\nM = 11\nU = 00\nR = $\n\n[rules]\nS0 < M M -> S0 < D1\nD1 < M M -> D1 < D1\nc> M M -> c> D1\ne> M M -> e> D1\nS0 < M U -> S0 < D0\nD1 < M U -> D1 < D0\nc> M R -> c> D0 R\ne> M R -> e> D0 R\nD1 <a -> < D1\nc> M D0 -> c> D1 U\ne> M D0 -> e> D1 U\n\nX < -> < X\nL < -> L X X c>\nc> X -> X c>\n\nD1 < -> < D1\nS0 < -> < D0\n\nc> D0 -> S0 e>\ne> D0 -> D1 c>\n\nc> D1 -> D1 c>\ne> D1 -> S0 e>\n\nc> K -> M J D>\ne> K -> M e>\nF> K -> M B>\nD> K -> J E>\nE> K -> e>\na> K -> <C K J\n\nc> J -> K K F>\ne> J -> < M\nF> J -> M D>\nD> J -> M D>\nB> J -> c>\nE> J -> <C M\n\nc> M -> M c>\ne> M -> M K F>\nF> M -> e>\nD> M -> a>\nE> M -> K F>\na> M -> J M D>\n\nc> U -> K e>\ne> U -> < K\nF> U -> <a\nD> U -> <a\nB> U -> J D>\nE> U -> <C K\na> U -> J c>\n\nc> R -> <a U K R\ne> R -> < K R\nF> R -> <a R\nD> R -> <a R\nB> R -> <C K J R\nE> R -> <C K R\na> R -> <C K J U K R\n\nK < -> <a U\nK <a -> M c>\nK <C -> M D>\n\nM < -> < M\nM <a -> < M\nM <C -> <\n\nJ < -> <C K J\nJ <a -> <C K J\nJ <C -> c>\n\nD> D1 -> J M D>\nF> D1 -> M K F>\na> D1 -> J M a>\n\nD> D0 -> J c>\nF> D0 -> < K\na> D0 -> <C K J M\n";
const rules=[{"line":"S0 < M M -> S0 < D1","mult":0,"variable":false},{"line":"D1 < M M -> D1 < D1","mult":0,"variable":false},{"line":"c> M M -> c> D1","mult":0,"variable":false},{"line":"e> M M -> e> D1","mult":0,"variable":false},{"line":"S0 < M U -> S0 < D0","mult":0,"variable":false},{"line":"D1 < M U -> D1 < D0","mult":0,"variable":false},{"line":"c> M R -> c> D0 R","mult":0,"variable":false},{"line":"e> M R -> e> D0 R","mult":0,"variable":false},{"line":"D1 <a -> < D1","mult":16,"variable":false},{"line":"c> M D0 -> c> D1 U","mult":0,"variable":false},{"line":"e> M D0 -> e> D1 U","mult":0,"variable":false},{"line":"X < -> < X","mult":5,"variable":true},{"line":"L < -> L X X c>","mult":11,"variable":false},{"line":"c> X -> X c>","mult":3,"variable":true},{"line":"D1 < -> < D1","mult":20,"variable":false},{"line":"S0 < -> < D0","mult":8,"variable":false},{"line":"c> D0 -> S0 e>","mult":8,"variable":false},{"line":"e> D0 -> D1 c>","mult":10,"variable":false},{"line":"c> D1 -> D1 c>","mult":12,"variable":false},{"line":"e> D1 -> S0 e>","mult":6,"variable":false},{"line":"c> K -> M J D>","mult":4,"variable":false},{"line":"e> K -> M e>","mult":2,"variable":false},{"line":"F> K -> M B>","mult":2,"variable":false},{"line":"D> K -> J E>","mult":2,"variable":false},{"line":"E> K -> e>","mult":2,"variable":false},{"line":"a> K -> <C K J","mult":7,"variable":false},{"line":"c> J -> K K F>","mult":2,"variable":false},{"line":"e> J -> < M","mult":3,"variable":false},{"line":"F> J -> M D>","mult":2,"variable":false},{"line":"D> J -> M D>","mult":2,"variable":false},{"line":"B> J -> c>","mult":4,"variable":false},{"line":"E> J -> <C M","mult":1,"variable":false},{"line":"c> M -> M c>","mult":6,"variable":false},{"line":"e> M -> M K F>","mult":2,"variable":false},{"line":"F> M -> e>","mult":4,"variable":false},{"line":"D> M -> a>","mult":2,"variable":false},{"line":"E> M -> K F>","mult":2,"variable":false},{"line":"a> M -> J M D>","mult":4,"variable":false},{"line":"c> U -> K e>","mult":2,"variable":false},{"line":"e> U -> < K","mult":3,"variable":false},{"line":"F> U -> <a","mult":3,"variable":false},{"line":"D> U -> <a","mult":3,"variable":false},{"line":"B> U -> J D>","mult":2,"variable":false},{"line":"E> U -> <C K","mult":1,"variable":false},{"line":"a> U -> J c>","mult":2,"variable":false},{"line":"c> R -> <a U K R","mult":7,"variable":false},{"line":"e> R -> < K R","mult":3,"variable":false},{"line":"F> R -> <a R","mult":3,"variable":false},{"line":"D> R -> <a R","mult":3,"variable":false},{"line":"B> R -> <C K J R","mult":7,"variable":false},{"line":"E> R -> <C K R","mult":1,"variable":false},{"line":"a> R -> <C K J U K R","mult":11,"variable":false},{"line":"K < -> <a U","mult":2,"variable":false},{"line":"K <a -> M c>","mult":5,"variable":false},{"line":"K <C -> M D>","mult":1,"variable":false},{"line":"M < -> < M","mult":10,"variable":false},{"line":"M <a -> < M","mult":6,"variable":false},{"line":"M <C -> <","mult":2,"variable":false},{"line":"J < -> <C K J","mult":6,"variable":false},{"line":"J <a -> <C K J","mult":2,"variable":false},{"line":"J <C -> c>","mult":3,"variable":false},{"line":"D> D1 -> J M D>","mult":6,"variable":false},{"line":"F> D1 -> M K F>","mult":6,"variable":false},{"line":"a> D1 -> J M a>","mult":6,"variable":false},{"line":"D> D0 -> J c>","mult":4,"variable":false},{"line":"F> D0 -> < K","mult":7,"variable":false},{"line":"a> D0 -> <C K J M","mult":19,"variable":false}];

"use strict";
const assert = require("node:assert/strict");
/**
 * The source-listed 67 block rules are locally tested against an independent
 * primitive-step tape implementation. All data pin jhuang97/turing_machine
 * at 6aeb2384173cf4c93a9a7c7f418bb9b7b1839b39.
 * This is finite semantic evidence, NOT a proof of the complete accelerated
 * blank-orbit computation or an exact BB(6) score.
 *
 * @typedef {{ bit:string,head:number,state:string,ones:number[] }} Config
 */
const blocks={}, meta={}, machine={};
let section="";
for(const s0 of definition.split("\n")){
 const s=s0.trim();
 if(["[blocks]","[metastates]","[rules]"].includes(s)){section=s;continue;}
 if(!s||s.startsWith("tm ="))continue;
 if(section==="[blocks]"){const [a,b]=s.split(/\s*=\s*/);blocks[a.replace("(exp)","")]=b;}
 if(section==="[metastates]"){const [,tok,...rest]=s.split(/\s+/);meta[tok]=rest.join("");}
}
const tm=definition.split("\n")[0].slice(5).split("_");
assert.equal(tm.length,6);
for(let i=0;i<6;i++)for(let b=0;b<2;b++)machine[String.fromCharCode(65+i)+b]=tm[i].slice(b*3,b*3+3);
const declared=definition.split("\n").filter(s=>s.includes("->"));
assert.deepEqual(rules.map(x=>x.line),declared);
assert.equal(rules.length,67);
/** @param {string[]} ts @param {number} n @returns {Config} */
function expand(ts,n){
 let bit="",head=-1,state="";
 for(const token of ts){
  if(token==="L"||token==="R")continue;
  if(Object.hasOwn(meta,token)){
   const p=meta[token].match(/^(.*?)(?:<([A-F])|([A-F])>)(.*)$/);
   assert.ok(p,"Bad metastate "+token);
   head=bit.length+p[1].length+(p[2]?-1:0);state=p[2]||p[3];bit+=p[1]+p[4];
  }else{const v=blocks[token];assert.ok(v!==undefined,"Bad block "+token);bit+=token==="X"?v.repeat(n):v;}
 }
 return{bit,head,state,ones:[...bit].flatMap((x,i)=>x==="1"?[i]:[])};
}
/** @param {Config} c @param {number} n */
function run(c,n){
 let h=c.head,s=c.state;const tape=new Set(c.ones);
 for(let k=0;k<n;k++){
  const x=machine[s+(tape.has(h)?1:0)];
  if(x==="---")return {h,s,tape,halted:k};
  if(x[0]==="1")tape.add(h);else tape.delete(h);
  h+=x[1]==="R"?1:-1;s=x[2];
 }
 return{h,s,tape,halted:null};
}
/** @param {ReturnType<typeof run>} r @param {Config} wanted */
function equal(r,wanted){
 assert.equal(r.halted,null,"premature halt");
 assert.equal(r.s,wanted.state,"control state");
 assert.deepEqual([...r.tape].map(i=>i-r.h).sort((a,b)=>a-b),
  wanted.ones.map(i=>i-wanted.head).sort((a,b)=>a-b),"relative complete tape");
}
const contexts=[[],["M"],["U"],["K","J"],["D0","S0"],["X"],["D1","M","U"]];
let tested=0;
for(const rule of rules){
 const [a,b]=rule.line.split(" -> ").map(s=>s.split(" "));
 for(const n of rule.variable?[1,2,5]:[1])for(const l of contexts)for(const r of contexts){
  const pre=a[0]==="L"?[]:["L",...l],post=a.at(-1)==="R"?[]:[...r,"R"];
  try{
   equal(run(expand([...pre,...a,...post],n),rule.mult*(rule.variable?n:1)),
     expand([...pre,...b,...post],n));
  }catch(e){throw Error("Rule "+rule.line+" n="+n+" left="+l+" right="+r+": "+e);}
  tested++;
 }
}
equal(run({bit:"",head:0,state:"A",ones:[]},42),
      expand(["L","X","c>","D0","M","K","R"],1));
for(const block of ["K","M"]){
 const c=expand(["L","B>",block,"R"],1);
 assert.equal(machine[c.state+(c.ones.includes(c.head)?1:0)],"---");
}
const c=expand(["L","a>","J","R"],1),o=run(c,1);
assert.equal(o.halted,null);
assert.equal(machine[o.s+(o.tape.has(o.h)?1:0)],"---");
assert.equal(tested,3479);
console.log("PASS: 67 textual block rules; "+tested+" exact local raw comparisons; blank-A step 42; 3 local terminal guards.");
console.log("Finite test only; full accelerated trace and unlimited contexts remain uncertified.");
