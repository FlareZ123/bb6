'use strict';
const fs = require('node:fs');
const assert = require('node:assert/strict');
const moves = Array.from({length:24},(_,i)=>[i>=12?1:0,(i%12)>=6?1:-1,i%6]);
const parentRle='1RB---_1RC1LF_0RD0RB_1LD1RE_---0LB_---0LA';
const graftRle='1RB---_1RC1LF_0RD0RB_1LD1RE_---0LB_0LE0LA';
const decode=rle=>rle.split('_').flatMap(s=>[s.slice(0,3),s.slice(3)]).map(a=>a==='---'?null:[+a[0],a[1]==='R'?1:-1,a.charCodeAt(2)-65]);
const encode=t=>Array.from({length:6},(_,i)=>t.slice(2*i,2*i+2).map(a=>a===null?'---':String(a[0])+(a[1]>0?'R':'L')+String.fromCharCode(65+a[2])).join('')).join('_');
const parent=decode(parentRle);
const refine=(t,s,a)=>t.map((x,i)=>i===s?a:x);
const same=(a,b)=>a.size===b.size&&[...a].every(x=>b.has(x));
/** Return exact observed first hole or exact translated half-line recurrence. */
function witness(t,limit=600,periodLimit=128){
  let q=0,h=0;const ones=new Set(),history=[],exact=new Map();
  for(let n=0;n<=limit;n++){
    const f=new Set(ones),key=JSON.stringify([q,h,[...f].sort((a,b)=>a-b)]);
    if(exact.has(key)){
      const entry=exact.get(key);
      return {kind:'cycle',entry,period:n-entry,right:true,boundary:Math.min(...history.slice(entry).map(x=>x.h))};
    }
    exact.set(key,n);
    let lo=h,hi=h;
    for(let j=n-1;j>=Math.max(0,n-periodLimit);j--){
      const c=history[j];lo=Math.min(lo,c.h);hi=Math.max(hi,c.h);
      if(c.q!==q)continue;
      const d=h-c.h;
      if(d>=0&&same(new Set([...c.f].filter(x=>x>=lo).map(x=>x+d)),new Set([...f].filter(x=>x>=lo+d))))return {kind:'cycle',entry:j,period:n-j,right:true,boundary:lo};
      if(d<=0&&same(new Set([...c.f].filter(x=>x<=hi).map(x=>x+d)),new Set([...f].filter(x=>x<=hi+d))))return {kind:'cycle',entry:j,period:n-j,right:false,boundary:hi};
    }
    history.push({q,h,f});
    const slot=q*2+Number(ones.has(h)),a=t[slot];
    if(a===null)return {kind:'hole',n,slot};
    if(a[0])ones.add(h);else ones.delete(h);
    h+=a[1];q=a[2];
  }
  return {kind:'open'};
}
/** Incoming zero-prefix delay: simple state paths ending at A, never repeat. */
function delays(t){
  function rec(q,visited){
    const out=new Set([0]);
    for(let p=0;p<6;p++){
      if(visited.has(p))continue;
      const a=t[2*p];
      if(a===null||(a[0]===0&&a[2]===q))for(const d of rec(p,new Set([...visited,p])))out.add(1+d);
    }
    return out;
  }
  return [...rec(0,new Set([0]))].sort((a,b)=>a-b);
}
function build(t){
  if(encode(t)===graftRle)return {kind:'graft'};
  const r=witness(t);
  if(r.kind!=='hole')return r;
  r.bound=r.n+1+Math.max(...delays(refine(t,r.slot,[-1,0,0])));
  if(t.filter(x=>x===null).length===1)return {...r,kind:'last'};
  return {...r,kind:'expand',children:moves.map(a=>build(refine(t,r.slot,a)))};
}
/** Independent certificate check: no search, exact specified trace, all siblings. */
function check(t,p,graft=true,path=[],report={expand:0,last:0,cycle:0,open:0,graft:0,haltMass:0,nonhaltMass:0,openMass:0,maxBound:0,unresolved:[]}){
  const holes=t.filter(x=>x===null).length;
  const trace=n=>{
    assert(Number.isSafeInteger(n)&&n>=0&&n<=10000);
    let q=0,h=0;const f=new Set(),cs=[];
    for(let i=0;i<=n;i++){
      cs.push({q,h,f:new Set(f)});
      if(i===n)break;
      const a=t[2*q+Number(f.has(h))];assert(a!==null,'premature hole');
      if(a[0])f.add(h);else f.delete(h);h+=a[1];q=a[2];
    }
    return cs;
  };
  assert(Object.hasOwn(report,p.kind),'unknown verdict');report[p.kind]++;
  switch(p.kind){
    case 'open':
      report.openMass+=25**holes;report.unresolved.push({path,rle:encode(t),holes});break;
    case 'graft':
      assert.equal(encode(t),graftRle,'graft table mismatch');
      if(graft){report.haltMass+=41;report.nonhaltMass+=584;report.maxBound=Math.max(report.maxBound,84);}
      else{report.graft--;report.open++;report.openMass+=625;report.unresolved.push({path,rle:encode(t),holes});}
      break;
    case 'cycle':{
      assert(p.period>0&&Number.isSafeInteger(p.period));assert(typeof p.right==='boolean'&&Number.isSafeInteger(p.boundary));
      const cs=trace(p.entry+p.period),c=cs[p.entry],d=cs.at(-1),delta=d.h-c.h,side=x=>p.right?x>=p.boundary:x<=p.boundary;
      assert(c.q===d.q&&(p.right?delta>=0:delta<=0),'bad orientation');
      assert(cs.slice(p.entry,-1).every(c=>side(c.h)),'read outside retained region');
      assert(same(new Set([...c.f].filter(side).map(x=>x+delta)),new Set([...d.f].filter(x=>side(x-delta)))),'tail mismatch');
      report.nonhaltMass+=25**holes;break;
    }
    case 'last':case 'expand':{
      const c=trace(p.n).at(-1);assert.equal(p.slot,c.q*2+Number(c.f.has(c.h)),'wrong queried slot');assert.equal(t[p.slot],null,'query not a hole');
      const bound=p.n+1+Math.max(...delays(refine(t,p.slot,[-1,0,0])));assert.equal(p.bound,bound,'wrong halt delay bound');
      report.maxBound=Math.max(report.maxBound,bound);
      if(p.kind==='last'){assert.equal(holes,1);report.haltMass++;report.nonhaltMass+=24;}
      else{assert(holes>1);assert.equal(p.children.length,24,'omitted or extra child');report.haltMass+=25**(holes-1);p.children.forEach((child,i)=>check(refine(t,p.slot,moves[i]),child,graft,[...path,i],report));}
      break;
    }
    default:throw Error('bad verdict');
  }
  return report;
}
function main(){
  const start=performance.now(),plan=build(parent),generated=performance.now();
  const before=check(parent,plan,false),after=check(parent,plan,true),checked=performance.now();
  for(const r of [before,after])assert.equal(r.haltMass+r.nonhaltMass+r.openMass,25**3);
  const mutations=[
    p=>p.children.pop(),
    p=>p.slot=1,
    p=>p.bound++,
    p=>p.children[0].children[0]={kind:'graft'},
    p=>p.children[2].period=0,
  ];
  for(const mutate of mutations){const bad=JSON.parse(JSON.stringify(plan));mutate(bad);assert.throws(()=>check(parent,bad));}
  if(process.argv.includes('--write'))fs.writeFileSync('plan.json',JSON.stringify(plan,null,0)+'\n');
  else assert.deepEqual(plan,JSON.parse(fs.readFileSync('plan.json','utf8')));
  console.log(JSON.stringify({parent:parentRle,source:'20db4dbe086ea0e6436eacbb5fab725957d3bda2',generationMs:generated-start,checkerMs:checked-generated,before,after,bytes:Buffer.byteLength(JSON.stringify(plan)),negativeControls:mutations.length},null,2));
}
main();
