"use strict";
const assert=require("node:assert/strict");
const {find,bank}=require("../agent5-weighted-tnf-queue/coarse-pair.cjs");
const data=require("../agent5-weighted-tnf-queue/q0-export/pilot-0-100-fuel-1000000.json");
const scan=require("../agent5-weighted-tnf-queue/q0-open-root-scan-2026-11-26.json");
const certs=require("../agent5-weighted-tnf-queue/q0-open-automata.json");
const moves=Array.from("ABCDEF").flatMap(q=>Array.from("01").flatMap(w=>Array.from("LR",d=>w+d+q)));
const state=s=>s.charCodeAt(2)-65;
const slot=(q,b)=>2*q+b;
const key=r=>r.join(",");
const parse=t=>t.replaceAll("_","").match(/.{3}/g);
const print=a=>a.join("").match(/.{6}/g).join("_");

// Independent absolute-coordinate tape replay, rather than the searcher's
// two BigInt stacks. Halt queries are counted separately from live moves.
function replay(a,n,entry=null){
  let q=0,h=0,ones=new Set(),before,min=Infinity,max=-Infinity;
  for(let j=0;j<=n;j++){
    if(j===entry)before={q,h,ones:new Set(ones)};
    if(entry!==null&&j>=entry){min=Math.min(min,h);max=Math.max(max,h);}
    const s=Number(ones.has(h)),i=slot(q,s),tr=a[i];
    if(j===n)return {q,h,ones,i,tr,before,min,max};
    assert.notEqual(tr,"---","early halt");
    if(tr[0]==="1")ones.add(h);else ones.delete(h);
    h+=tr[1]==="R"?1:-1;q=state(tr);
  }
}
function checkSide(a,t){
  const [,dir,e,p,k]=t,d=dir==="R"?1:-1;
  assert(p>0&&e>=0&&k>=0);
  const end=replay(a,e+p,e),start=end.before;
  assert.equal(end.q,start.q);
  assert(d*(end.h-start.h)>=0);
  assert((d===1?end.min-start.h:start.h-end.max)>=-k);
  const cone=(ones,h)=>new Set([...ones].map(x=>d*(x-h)).filter(x=>x>=-k));
  const x=cone(start.ones,start.h),y=cone(end.ones,end.h);
  assert.equal(x.size,y.size);
  assert([...x].every(v=>y.has(v)));
}

// Explicit finite-stack invariants: seed blank stacks, then check push
// edges and all possible pop successors. This checker is independent of
// the worklist and source encoder used by the certificate generator.
function checkCert(a,c){
  assert.equal(c.table,a.join(""));
  const ds=[c.left,c.right],rs=new Set(c.rows.map(key));
  for(const x of ds){
    assert(x.push.length>0);
    assert.equal(x.pop.length,x.push.length);
    for(const row of x.push){assert.equal(row.length,2);assert(row.every(i=>Number.isInteger(i)&&i>=0&&i<x.push.length));}
    for(const es of x.pop)for(const [b,i] of es){assert(b===0||b===1);assert(Number.isInteger(i)&&i>=0&&i<x.push.length);}
    assert(x.pop[0].some(([b,i])=>b===0&&i===0));
  }
  assert(rs.has("0,0,0,0"));
  for(const [q,b,l,r] of c.rows){
    assert(Number.isInteger(q)&&q>=0&&q<6&&(b===0||b===1));
    assert(Number.isInteger(l)&&l>=0&&l<ds[0].push.length);
    assert(Number.isInteger(r)&&r>=0&&r<ds[1].push.length);
    const tr=a[slot(q,b)];
    assert.notEqual(tr,"---","abstract halt");
    const w=+tr[0],n=state(tr),d=tr[1]==="R"?1:0;
    const old=d?l:r,to=ds[1-d].push[old][w];
    assert(ds[1-d].pop[to].some(([v,i])=>v===w&&i===old));
    for(const [v,i] of ds[d].pop[d?r:l]){
      const next=d?[n,v,to,i]:[n,v,i,to];
      assert(rs.has(key(next)),"abstract successor missing");
    }
  }
}

// Reconstruct the 55 coarse DFA certificates using full fixed-point
// sweeps, not the searcher's incremental waiter queues.
function saturate(a,L,R){
  const push=[L,R],pop=push.map(d=>d.map(()=>new Set())),rows=new Map();
  const add=r=>{const k=key(r);if(rows.has(k))return false;rows.set(k,r);return true;};
  pop[0][0].add(0);pop[1][0].add(0);add([0,0,0,0]);
  let changed;
  do{
    changed=false;
    for(const [q,b,l,r] of [...rows.values()]){
      const tr=a[slot(q,b)];assert.notEqual(tr,"---","coarse abstract halt");
      const w=+tr[0],n=state(tr),d=tr[1]==="R"?1:0,old=d?l:r,to=push[1-d][old][w],edge=2*old+w;
      if(!pop[1-d][to].has(edge)){pop[1-d][to].add(edge);changed=true;}
      for(const v of pop[d][d?r:l]){
        const s=v%2,i=v>>1;
        if(add(d?[n,s,to,i]:[n,s,i,to]))changed=true;
      }
    }
  }while(changed);
  const stack=i=>({push:push[i],pop:pop[i].map(es=>[...es].map(v=>[v%2,v>>1]))});
  return {table:a.join(""),left:stack(0),right:stack(1),rows:[...rows.values()]};
}

// In a completion with first halt slot h fixed undefined, possible
// zero-writing outgoing edges are exactly these. Since A0 writes 1,
// a deterministic zero-writing path to A has distinct states. Each
// simple path in the possible graph can be realized by choosing the
// previously unassigned transition at each distinct state.
function delay(a,h){
  assert.equal(a[0][0],"1");
  const edges=Array.from({length:6},(_,q)=>{
    const i=2*q,tr=a[i];
    return i===h?[]:tr==="---"?[0,1,2,3,4,5]:tr[0]==="0"?[state(tr)]:[];
  });
  let best=[0];
  function back(p){
    if(p.length>best.length)best=p;
    for(let q=0;q<6;q++)if(!p.includes(q)&&edges[q].includes(p[0]))back([q,...p]);
  }
  back([0]);return best;
}
function witness(rec){
  let a=parse(rec.table);
  for(let j=0;j+1<rec.path.length;j++){
    const i=2*rec.path[j],r=rec.path[j+1];
    if(a[i]==="---")a[i]="0R"+"ABCDEF"[r];
    assert.equal(a[i][0],"0");assert.equal(state(a[i]),r);
  }
  a=a.map((tr,i)=>tr==="---"&&i!==rec.h?"1RA":tr);
  const c=replay(a,rec.n);
  assert.equal(c.i,rec.h);assert.equal(c.tr,"---");
  return {table:print(a),liveMoves:rec.n,haltSlot:"ABCDEF"[rec.h>>1]+rec.h%2,
    standardScore:rec.n+1,weightedScore:rec.n+rec.path.length,
    zeroPath:rec.path.map(q=>"ABCDEF"[q]).join("")};
}
function run(index=33){
  const root=scan.results.find(x=>x.index===index);
  assert(root);
  const row=data.active[index];assert.equal(row.table,root.table);
  const a=parse(row.table);
  assert.equal(a.filter(x=>x==="---").length,row.holes);
  const {tree,n}=find(row,true);assert(tree);assert.equal(n,root.stats.nodes);
  const open=new Map(root.openTables.map((x,i)=>[x.table,certs["R"+index+"L"+i]]));
  const seen=new Map(),counts={nodes:0,side:0,mitm:0,last:0,split:0,open:0},hist={},halts=[];
  let bestRaw=null,bestWeight=null;
  function visit(t,a){
    counts.nodes++;
    if(t[0]==="s"){checkSide(a,t);counts.side++;return;}
    if(t[0]==="p"){checkCert(a,saturate(a,bank[t[1]],bank[t[2]]));counts.mitm++;return;}
    if(t[0]==="o"){
      const c=open.get(t[1]);assert(c);checkCert(a,c);
      seen.set(t[1],1+(seen.get(t[1])||0));counts.open++;return;
    }
    assert.equal(t[0],"h");
    const [,n,h,kids]=t,c=replay(a,n);
    assert.equal(c.i,h);assert.equal(c.tr,"---");
    const path=delay(a,h),k=path.length-1,rec={table:print(a),n,h,path,weighted:n+1+k};
    hist[k]=(hist[k]||0)+1;halts.push(rec);
    if(!bestRaw||n>bestRaw.n)bestRaw=rec;
    if(!bestWeight||rec.weighted>bestWeight.weighted)bestWeight=rec;
    if(!kids.length){assert.equal(a.filter(x=>x==="---").length,1);counts.last++;return;}
    assert.equal(kids.length,24);counts.split++;
    kids.forEach((child,j)=>{const b=a.slice();b[h]=moves[j];visit(child,b);});
  }
  visit(tree,a);
  for(const k of Object.keys(counts))assert.equal(counts[k],root.stats[k]);
  assert.equal(seen.size,root.openTables.length);
  for(const x of root.openTables)assert.equal(seen.get(x.table),x.count);
  assert(bestRaw&&bestWeight);
  return {index,parent:row.table,counts,haltBranches:halts.length,delayHistogram:hist,
    standardMaximum:bestRaw.n+1,weightedMaximum:bestWeight.weighted,
    standardWitness:witness(bestRaw),weightedWitness:witness(bestWeight),
    highHaltBranches:halts.filter(x=>x.n+6>bestWeight.weighted)};
}
if(require.main===module)console.log(JSON.stringify(run(Number(process.argv[2]||33)),null,2));
module.exports={run};
