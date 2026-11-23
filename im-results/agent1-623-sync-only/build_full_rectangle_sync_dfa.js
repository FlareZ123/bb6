#!/usr/bin/env node
"use strict";

function build(branch) {
  const amin = branch === "L" ? -2 : -4;
  const amax = branch === "L" ? 2 : 1;
  const ac = amax - amin + 1;
  const n = 9 * ac * 5;
  const next = Array.from({length:n}, () => Array(9).fill(-1));
  for (let xp=0; xp<3; xp++) for (let yp=0; yp<3; yp++)
  for (let a=amin; a<=amax; a++) for (let b=-2; b<=2; b++) {
    const s = (((xp*3+yp)*ac + (a-amin))*5 + (b+2));
    for (let x=0; x<3; x++) for (let y=0; y<3; y++) {
      let tx,ty;
      if (branch === "L") { tx=x-yp+a; ty=yp+b; }
      else { tx=-x-xp-yp+a; ty=xp+yp+b; }
      const an=Math.floor(tx/3), bn=Math.floor(ty/3);
      if (an<amin || an>amax || bn< -2 || bn>2)
        throw new Error("carry rectangle is not closed");
      next[s][3*x+y] = (((x*3+y)*ac + (an-amin))*5 + (bn+2));
    }
  }
  return {amin,amax,n,next};
}

function stepSet(xs,T,z) {
  return [...new Set(xs.map(s => T.next[s][z]))].sort((a,b)=>a-b);
}
const pairKey = (l,r) => l.join(",") + "|" + r.join(",");

const L=build("L"), R=build("R");
const states=[{
  L:[...Array(L.n).keys()],
  R:[...Array(R.n).keys()],
  rep:[]
}];
const ids=new Map([[pairKey(states[0].L,states[0].R),0]]);
const transitions=[];

for (let i=0; i<states.length; i++) {
  const row=[];
  for (let z=0; z<9; z++) {
    const l=stepSet(states[i].L,L,z);
    const r=stepSet(states[i].R,R,z);
    const key=pairKey(l,r);
    let j=ids.get(key);
    if (j === undefined) {
      j=states.length;
      ids.set(key,j);
      states.push({L:l,R:r,rep:states[i].rep.concat(z)});
    }
    row.push(j);
  }
  transitions.push(row);
}

let cls=states.map(s => s.L.length===1 && s.R.length===1 ? 1 : 0);
const refinement=[2];
for (let it=0; it<20; it++) {
  const sigIds=new Map(), nextCls=[];
  for (let s=0; s<states.length; s++) {
    const sig=cls[s]+"|"+transitions[s].map(t=>cls[t]).join(",");
    if (!sigIds.has(sig)) sigIds.set(sig,sigIds.size);
    nextCls[s]=sigIds.get(sig);
  }
  refinement.push(sigIds.size);
  let stable=true;
  outer: for (let i=0; i<states.length; i++)
    for (let j=i+1; j<states.length; j++)
      if ((cls[i]===cls[j]) !== (nextCls[i]===nextCls[j])) {
        stable=false; break outer;
      }
  cls=nextCls;
  if (stable) break;
}

const N=Math.max(...cls)+1;
const reps=Array(N).fill(-1);
for (let s=0; s<states.length; s++) if (reps[cls[s]]<0) reps[cls[s]]=s;
const out={
  schema:"bb6.machine623.full-rectangle-sync-dfa.v1",
  alphabet:{size:9,encoding:"symbol=3*x+y"},
  sourceRectangles:{L:{states:L.n},R:{states:R.n}},
  reachableSubsetPairStates:states.length,
  reachableShortestRepresentativeMax:Math.max(...states.map(s=>s.rep.length)),
  minimizedStateCount:N,
  minimizationRefinementCounts:refinement,
  initialState:cls[0],
  acceptingStates:[...Array(N).keys()].filter(c => {
    const s=states[reps[c]];
    return s.L.length===1 && s.R.length===1;
  }),
  transitions:reps.map(s => transitions[s].map(t=>cls[t])),
  representativeWords:reps.map(s=>states[s].rep),
  representativeRanks:reps.map(s=>[states[s].L.length,states[s].R.length])
};
if (out.reachableSubsetPairStates!==355 || out.minimizedStateCount!==70 ||
    out.acceptingStates.length!==1 || out.acceptingStates[0]!==53)
  throw new Error("construction regression");
console.log(JSON.stringify(out,null,2));
