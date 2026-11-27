/* Consume, rather than rediscover, every saved proof on an A1=0LA canonical child.
   Load after discover_compact.js, far_search.js and recipe_decode.js.
   Exhaustive finite audit; mathematical nonhalting lemmas are separately documented.
   No Lean acceptance is implied. */
function auditAssert(ok,msg){if(!ok)throw Error(msg)}
function auditReplay(table,n){
 let p=parse(table),t=new Set(),q=0,h=0,steps=0;
 for(;steps<n;steps++){let s=2*q+Number(t.has(h)),m=p[s];auditAssert(m>=0,"early hole "+table+" "+steps);if(m>=12)t.add(h);else t.delete(h);h+=m%12>=6?1:-1;q=m%6}
 return {p,t,q,h,s:2*q+Number(t.has(h))};
}
function auditDelay(p,state=0,seen=1){let best=[];for(let q=0;q<6;q++)if(!(seen>>q&1)){let a=p[2*q];if(a===-1||(a>=0&&a<12&&a%6===state)){let x=[q,...auditDelay(p,q,seen|(1<<q))];if(x.length>best.length)best=x}}return best}
function auditLate(table,r){
 let a=auditReplay(table,r.n),p=a.p.slice();auditAssert(p.filter(x=>x<0).length===1&&a.s===r.slot&&p[a.s]===-1,"late hole mismatch");
 p[a.s]=-2;let d=auditDelay(p);if(r.delay!==undefined)auditAssert(d.length===r.delay,"delay mismatch");return {score:r.n+1+d.length,n:r.n,slot:r.slot,delay:d.length,delayPath:d,table:table.replaceAll("_","").match(/.../g).map((m,i)=>i===a.s?"HHH":m).join("").match(/.{6}/g).join("_")}
}
function auditCycle(table,c){
 let a=auditReplay(table,c.entry),{p,q,h,t}=a,t0=new Set(t),q0=q,h0=h;
 let low=h,high=h;for(let i=0;i<c.period;i++){let m=p[2*q+Number(t.has(h))];auditAssert(m>=0,"cycle hole");if(m>=12)t.add(h);else t.delete(h);h+=m%12>=6?1:-1;q=m%6;low=Math.min(low,h);high=Math.max(high,h)}
 let d=h-h0,b=c.bound,right=c.right;
 auditAssert(c.period>0&&q===q0&&d===c.shift&&(c.entryHead===undefined||h0===c.entryHead),"cycle endpoint");
 auditAssert(right?d>=0&&low>=b:d<=0&&high<=b,"cycle side");
 const half=x=>right?x>=b:x<=b;
 for(let x of t0)if(half(x))auditAssert(t.has(x+d),"cycle missing 1");
 for(let y of t)if(half(y-d))auditAssert(t0.has(y-d),"cycle extra 1");
 return true
}
function auditBankArray(z,n){let a=inflateZlib(b64(z));auditAssert(a.length===2*n,"bad bank index length");return Array.from({length:n},(_,i)=>a[2*i]+256*a[2*i+1])}
function auditSummary(a){let [k,r,c0,c1,m0,m1]=a;return r===0?ngram(k):k===0?rungram([r,c0,c1,m0,m1]):laggram(a)}
function auditChild(recipe,child,external,{cap=300000,emit=false}={}){
 let e=enumerate(recipe.parent);auditAssert(!e.stopped&&e.openCount===recipe.opens&&e.maxScore===recipe.initialBound,"enumerator mismatch "+child+" "+JSON.stringify([e.openCount,e.maxScore]));let tables=e.opens.map(x=>x[1]),covered=new Map(),counts={},proofs=[],best=e.maxWitness,B=e.maxScore;
 function mark(id,kind,table){auditAssert(Number.isInteger(id)&&id>=0&&id<tables.length&&!covered.has(id),"duplicate or invalid ID "+child+"/"+id);if(table!==undefined)auditAssert(tables[id]===table,"literal mismatch "+child+"/"+id);covered.set(id,kind);counts[kind]=(counts[kind]||0)+1;return tables[id]}
 function far(id,code,table){let t=mark(id,"far",table),D=Array.from(code.slice(1),Number),rev=Number(code[0]);auditAssert(D.length%2===0&&D.length<=10&&D[0]===0&&D.every(x=>Number.isInteger(x)&&x>=0&&x<D.length/2)&&(rev===0||rev===1)&&farCheck(t,D,rev),"FAR reject "+child+"/"+id);if(emit)proofs.push({id,kind:"far",table:t,code})}
 function compact(id,fs,table,old){let t=mark(id,"compact",table),r=solve(t,fs,cap);auditAssert(r.ok,"compact reject "+child+"/"+id);if(old)auditAssert(r.states===old.states&&r.edges===old.edges,"compact count mismatch "+child+"/"+id);if(emit)proofs.push({id,kind:"compact",table:t,dfa:r.dfa,states:r.states,edges:r.edges})}
 function late(r){let t=mark(r.id,"late",r.table),w=auditLate(t,r);if(w.score>B){B=w.score;best=w}if(emit)proofs.push({kind:"late",...r,table:t,delay:w.delay})}
 function cycle(r){let t=mark(r.id,"cycle",r.table);auditCycle(t,r);if(emit)proofs.push({kind:"cycle",...r,table:t})}
 function unresolved(id,table){let x=external[child+"/"+id];auditAssert(x,"unresolved "+child+"/"+id);let t=mark(id,x.kind,table);auditAssert(x.table===t,"external literal mismatch");if(x.kind==="long-cycle")auditCycle(t,x);if(emit)proofs.push({...x,id,table:t});}
 if(recipe.farZ){let farI=auditBankArray(recipe.farZ,tables.length),compactI=auditBankArray(recipe.compactZ,tables.length);for(let i=0;i<tables.length;i++){if(farI[i])far(i,recipe.farBank[farI[i]-1]);if(compactI[i]){let a=recipe.compactBank[compactI[i]-1];compact(i,[auditSummary(a.slice(0,6)),auditSummary(a.slice(6))])}}for(let r of recipe.cycles)cycle(r);for(let r of recipe.late)late(r);for(let id of recipe.unresolved)unresolved(id)}
 else {for(let r of recipe.far)far(r.id,r.code,r.table);for(let r of recipe.compact)compact(r.id,r.dfa.map(D=>({start:0,fn:(s,b)=>D[2*s+b]})),r.table,r);for(let r of recipe.late)late(r);for(let r of recipe.unresolved)unresolved(r.id,r.table)}
 auditAssert(covered.size===tables.length,"incomplete coverage "+child+" missing "+tables.map((_,i)=>i).filter(i=>!covered.has(i)).slice(0,20));
 if(recipe.boundCandidate!==undefined)auditAssert(recipe.boundCandidate===B,"candidate mismatch");
 return {child,opens:tables.length,nodes:e.nodes,initialBound:e.maxScore,bound:B,witness:best,counts,...(emit?{proofs}:{} )}
}
