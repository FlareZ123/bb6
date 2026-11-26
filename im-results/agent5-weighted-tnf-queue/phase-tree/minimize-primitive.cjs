"use strict";
// A partial-push quotient heuristic. Every returned certificate is recomputed
// and checked by primitive MITM closure, so greedy merging is untrusted.
const {mitmCert}=require("../q0-open-automata.cjs");
function trim(c){
 return [c.left,c.right].map((s,side)=>{
  let states=[...new Set([0,...c.rows.map(r=>r[2+side])])].sort((a,b)=>a-b),ids=new Map(states.map((x,i)=>[x,i])),required=new Set([0]);
  for(let [q,a,l,r] of c.rows){let m=c.table.slice(6*q+3*a,6*q+3*a+3);if(side===Number(m[1]==="L"))required.add(2*[l,r][side]+Number(m[0]))}
  return states.map(i=>[0,1].map(b=>required.has(2*i+b)?ids.get(s.push[i][b]):-1))
 })
}
function minimizeOne(table,dl,dr,side,maxTries=3000){
 let [a,b]=side?[dr,dl]:[dl,dr],n=a.length,roots=Array.from({length:n},(_,i)=>i),trans=a.map(x=>x.slice()),attempts=0,merges=0;
 function find(p,x){while(p[x]!==x)x=p[x];return x}
 function merge(p,tr,i,j){
  let todo=[[i,j]];
  while(todo.length){let [u,v]=todo.pop();u=find(p,u);v=find(p,v);if(u===v)continue;if(u>v)[u,v]=[v,u];p[v]=u;
   for(let x=0;x<2;x++){let y=tr[u][x],z=tr[v][x];if(y===-1)tr[u][x]=z;else if(z!==-1)todo.push([y,z])}
  }
 }
 function dense(p,tr){let states=Array.from({length:n},(_,i)=>i).filter(i=>p[i]===i),ids=new Map(states.map((i,j)=>[i,j])),dead=states.length;return [...states.map(i=>tr[i].map(x=>x<0?dead:ids.get(find(p,x)))),[dead,dead]]}
 const complete=ds=>[...ds.map(t=>t.map(x=>x<0?ds.length:x)),[ds.length,ds.length]],bf=complete(b);
 for(let i=0;i<n&&attempts<maxTries;i++)if(roots[i]===i)for(let j=i+1;j<n&&attempts<maxTries;j++)if(roots[j]===j){
  let p=roots.slice(),tr=trans.map(x=>x.slice());merge(p,tr,i,j);let d=dense(p,tr);attempts++;
  let c=side?mitmCert(table,bf,d):mitmCert(table,d,bf);if(c){roots=p;trans=tr;merges++}
 }
 let d=dense(roots,trans),c=side?mitmCert(table,bf,d):mitmCert(table,d,bf);if(!c)throw Error("quotient closure regression");
 return c
}
function minimize(c,passes=[0,1,0,1]){for(let side of passes)c=minimizeOne(c.table,...trim(c),side);return c}
module.exports={minimize};
if(require.main===module){let fs=require("node:fs"),c=JSON.parse(fs.readFileSync(process.argv[2],"utf8"));process.stdout.write(JSON.stringify(minimize(c))+"\n")}
