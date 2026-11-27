// Raw40 0LA/0RD leaf154: exact finite premises for two simultaneous pumps.
const table="1RB0LA_1RC1RE_0RD0RD_1LD1LA_---0RF_0RC0RA";
const tr=table.replaceAll("_","").match(/.../g);
function assert(x,msg){if(!x)throw Error(msg)}
function replay(t,h,q,n,record=false){
 const edges=new Map(),depart=new Map();
 for(let i=0;i<n;i++){
  const m=tr[2*q+Number(t.has(h))];assert(m!=="---","unassigned move "+i);
  const d=m[1]==="R"?1:-1;
  if(m[0]==="1")t.add(h);else t.delete(h);
  q=m.charCodeAt(2)-65;
  if(record){
   const x=Math.min(h,h+d);
   edges.set(x,(edges.get(x)||"")+(d===1?"R":"L")+q);
   depart.set(h,(depart.get(h)||0)+1);
  }
  h+=d;
 }
 return {t,h,q,edges,depart};
}
function word(t,h){
 assert([...t].every(x=>x>h),"nonblank left or scanned cell");
 return Array.from({length:Math.max(h,...t)-h},(_,i)=>t.has(h+i+1)?"1":"0").join("");
}
const z=n=>"0".repeat(n),o=n=>"1".repeat(n),block=(g,b)=>z(g)+o(b);
const P=block(27,5)+block(3,10)+block(23,5);
const A=block(3,5),B=block(7,5);
const M=[7,7,15,7,27,3,7,7,11,7,3,11,7,7,7,3,11,7,3,7,11,11,3].map(g=>block(g,5)).join("");
const S=block(7,10);
function family(n){return P+A.repeat(14+n)+M+B.repeat(10+2*n)+S}
const entry=replay(new Set(),0,0,132476);
assert(entry.h===-480&&entry.q===0,"entry head/state");
assert(word(entry.t,entry.h)===family(0),"entry word");
const end=replay(new Set([...entry.t].map(x=>x-entry.h)),0,0,12262,true);
assert(end.h===-24&&end.q===0,"epoch head/state");
assert(word(end.t,end.h)===family(1),"epoch word");
const cuts=[[73,81],[489,513]], costs=[104,416];
const expected=["R3L3R4L0R3L3R4L0","R3L3R4L3R4L0R3L3R4L3R4L0R3L3R4L0"];
for(let i=0;i<cuts.length;i++){
 const [a,b]=cuts[i];
 assert(a>0&&a<b&&(i===0||cuts[i-1][1]<=a),"cut ordering");
 assert(end.edges.get(a)===expected[i]&&end.edges.get(b)===expected[i],"crossing mismatch");
 let count=0;for(let x=a+1;x<=b;x++)count+=end.depart.get(x)||0;
 assert(count===costs[i],"wrong departure count");
 // Each cut lies completely inside a periodic run at both endpoints.
 // End indices are translated by -end.h.
 for(let n=0;n<=1;n++){
  const base=i===0?P.length:P.length+(14+n)*A.length+M.length;
  const len=i===0?(14+n)*A.length:(10+2*n)*B.length;
  const offset=n===0?0:-end.h;
  assert(a+offset>=base&&b+offset<=base+len,"cut outside periodic run");
  assert((b-a)===(i===0?A.length:2*B.length),"wrong pump length");
 }
}
assert(costs.reduce((a,b)=>a+b,0)===520,"increment");
console.log("PASS: entry 132476, head -480; epoch 12262, shift -24; cuts 73..81, 489..513; increment 520");
