"use strict";
const fs=require("node:fs"),path=require("node:path");
const {find,bank}=require("./coarse-pair.cjs");
// Build a finite-stack certificate for the Coq source checker.  The
// Coq invariant checks the blank pop seeds and every transition row; unlike
// the Lean-side search helper, it does not require the DFA's blank push to
// be a self-loop.  The generated certificate is still rejected unless
// auto_cert_check evaluates to true in the original-source Coq kernel.
function sourceMitmCert(table,L,R){
 const ds=[L,R],E=ds.map(d=>d.map(()=>new Set())),W=ds.map(d=>d.map(()=>[])),seen=new Set(),rows=[],nr=R.length,nl=L.length;
 const key=(q,a,l,r)=>((2*q+a)*nl+l)*nr+r;
 function add(q,a,l,r){let k=key(q,a,l,r);if(!seen.has(k)){seen.add(k);rows.push([q,a,l,r]);}}
 function pop(st,e){let [q,a,l,r,n,d,w]=st,b=e%2,i=e>>1;if(d)add(n,b,L[l][w],i);else add(n,b,i,R[r][w]);}
 E[0][0].add(0);E[1][0].add(0);add(0,0,0,0);
 for(let i=0;i<rows.length;i++){
  let [q,a,l,r]=rows[i],t=table.slice(6*q+3*a,6*q+3*a+3);
  if(t==="---")return null;
  let w=+t[0],d=Number(t[1]==="R"),n=t.charCodeAt(2)-65,st=[q,a,l,r,n,d,w];
  let old=d?l:r,edge=2*old+w,dest=ds[1-d][old][w],set=E[1-d][dest];
  if(!set.has(edge)){set.add(edge);for(let waiter of W[1-d][dest])pop(waiter,edge);}
  let target=d?r:l;W[d][target].push(st);for(let e of E[d][target])pop(st,e);
 }
 for(let [q,a,l,r] of rows){
  let t=table.slice(6*q+3*a,6*q+3*a+3),w=+t[0],n=t.charCodeAt(2)-65;
  if(t[1]==="R"){
   let j=L[l][w];
   if(!E[0][j].has(2*l+w)||![...E[1][r]].every(e=>seen.has(key(n,e%2,j,e>>1))))throw Error("right closure");
  }else{
   let j=R[r][w];
   if(!E[1][j].has(2*r+w)||![...E[0][l]].every(e=>seen.has(key(n,e%2,e>>1,j))))throw Error("left closure");
  }
 }
 const stack=(d,i)=>({push:d,pop:E[i].map(es=>[...es].map(e=>[e%2,e>>1]))});
 return {table,left:stack(L,0),right:stack(R,1),rows};
}
const {encodeCert}=require("./q0-direct-auto.cjs");
const moves=Array.from("ABCDEF").flatMap(q=>Array.from("01").flatMap(w=>Array.from("LR").map(d=>w+d+q)));
const rootId=Number(process.argv[2]);
if(rootId>=55&&rootId<=58){require('./q0-periodic-parent.cjs').main(rootId,process.argv[3]||'Agent5Q0AutoData.v');process.exit(0);}
const scan=JSON.parse(fs.readFileSync(path.join(__dirname,"q0-open-root-scan-2026-11-26.json")));
const data=JSON.parse(fs.readFileSync(path.join(__dirname,"q0-export/pilot-0-100-fuel-1000000.json")));
const certs=JSON.parse(fs.readFileSync(path.join(__dirname,"q0-open-automata.json")));
const root=scan.results.find(r=>r.index===rootId && r.index!==28);
if(!root)throw Error("unknown target root "+rootId);
const row=data.active[rootId];
if(row.table!==root.table||row.holes!==root.holes||row.fresh!==root.fresh)throw Error("root identity mismatch");
const lookup=new Map(root.openTables.map((x,i)=>[x.table,certs["R"+rootId+"L"+i]]));
const {tree,n}=find(row,true);if(!tree)throw Error("tree generation aborted");
const observed=new Map();let direct=0;
function encode(t,a){
 if(t[0]==="o"){
  let c=lookup.get(t[1]);if(!c||c.table!==t[1]||c.table!==a.join(""))throw Error("missing exact leaf "+t[1]);
  observed.set(t[1],1+(observed.get(t[1])||0));direct++;
  return "SATcert ("+encodeCert(c)+")";
 }
 if(t[0]==="p"){let c=sourceMitmCert(a.join(""),bank[t[1]],bank[t[2]]);if(!c)throw Error("MITM certificate failed");direct++;return "SATcert ("+encodeCert(c)+")";}
 if(t[0]==="s")return "SATw (SWside "+t[1]+" "+t[2]+" "+t[3]+" "+t[4]+")";
 if(t[0]!=="h")throw Error("unknown branch "+t[0]);
 if(!t[3].length)return "SATw (SWlast "+t[1]+")";
 if(t[3].length!==24)throw Error("incomplete first-hole split");
 return "source_auto_split "+t[1]+" ("+"ABCDEF"[t[2]>>1]+",S"+t[2]%2+") ["+t[3].map((kid,j)=>{let b=a.slice();b[t[2]]=moves[j];return encode(kid,b)}).join(";\n")+"]";
}
// Root 33 previously stalled in a monolithic parent check.
const output=process.argv[3]||"Agent5Q0AutoData.v";
let shardManifest=null;
const body=(rootId===33||rootId===26)
  ? (shardManifest=require("./q0-direct-shards.cjs").emitShards({
      rootId,row,tree,bound:root.bound,encode,moves,output,
      chunkCap:rootId===26?1:25,timed:rootId===26
    }),null)
  : encode(tree,row.table.replaceAll("_","").match(/.{3}/g));
if(n!==root.stats.nodes||observed.size!==root.openTables.length||root.openTables.some(x=>observed.get(x.table)!==x.count))throw Error("open complement mismatch");
const out=[
"From BusyCoq Require Import Agent5SourceAutoTree.",
"From Coq Require Import List NArith Strings.String.",
"Import ListNotations.",
"Open Scope string_scope.",
"Open Scope nat_scope.",
"Definition auto_parent := TM_from_str \""+row.table+"\".",
"Definition auto_certificate : source_auto_tree := "+body+".",
"Definition auto_bound := "+root.bound+".",
"Lemma auto_checked : source_auto_check auto_bound auto_parent auto_certificate = true.",
"Proof. vm_compute. reflexivity. Qed.",
"Theorem auto_parent_safe : source_table_safe auto_bound auto_parent.",
"Proof. eapply source_auto_check_sound; exact auto_checked. Qed.",
"Print Assumptions auto_parent_safe."
].join("\n")+"\n";
if(!shardManifest)fs.writeFileSync(output,out);
console.log(JSON.stringify({rootId,table:row.table,n,bound:root.bound,open:observed.size,direct,...(shardManifest?{shardManifest}:{})}));
