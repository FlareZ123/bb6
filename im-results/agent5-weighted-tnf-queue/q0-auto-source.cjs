"use strict";
const fs=require("node:fs"),path=require("node:path");
const {find,emit,mitmPair}=require("./coarse-pair.cjs");
function total(s){const n=s.push.length;return [...s.push.map(([x,y],i)=>[x,y].map((j,b)=>s.pop[j].some(([a,k])=>a===b&&k===i)?j:n)),[n,n]]}
const rootId=Number(process.argv[2]);
if(rootId===52){require('./q0-root52.cjs');process.exit(0);}
if(rootId===53){require('./q0-root53.cjs');process.exit(0);}
const scan=JSON.parse(fs.readFileSync(path.join(__dirname,"q0-open-root-scan-2026-11-26.json")));
const data=JSON.parse(fs.readFileSync(path.join(__dirname,"q0-export/pilot-0-100-fuel-1000000.json")));
const certs=JSON.parse(fs.readFileSync(path.join(__dirname,"q0-open-automata.json")));
const root=scan.results.find(r=>r.index===rootId && r.index!==28);
if(!root)throw Error("unknown target root "+rootId);
const row=data.active[rootId];
if(row.table!==root.table||row.holes!==root.holes||row.fresh!==root.fresh)throw Error("root identity mismatch");
const lookup=new Map(root.openTables.map((x,i)=>[x.table,certs["R"+rootId+"L"+i]]));
const {tree,n}=find(row,true);if(!tree)throw Error("tree generation aborted");
const observed=new Map();
function hasOpen(t){return t[0]==="o"||(t[0]==="h"&&t[3].some(hasOpen))}
function listN(xs){return "["+xs.flat().map(n=>n+"%N").join(";")+"]"}
function encode(t){
 if(t[0]==="o"){
  let c=lookup.get(t[1]);if(!c||c.table!==t[1])throw Error("missing exact leaf "+t[1]);
  const l=total(c.left),r=total(c.right);
  if(!mitmPair(t[1].match(/.{3}/g),l,r))throw Error("DFA completion failed "+t[1]);
  observed.set(t[1],1+(observed.get(t[1])||0));
  return "ATdfa "+listN(l)+" "+listN(r);
 }
 if(!hasOpen(t))return "ATcoarse ("+emit(t)+")";
 if(t[0]!=="h"||t[3].length!==24)throw Error("incomplete first-hole split");
 return "auto_split "+t[1]+" ("+"ABCDEF"[t[2]>>1]+",S"+t[2]%2+") ["+t[3].map(encode).join(";\n")+"]";
}
const body=encode(tree);
if(n!==root.stats.nodes||observed.size!==root.openTables.length||root.openTables.some(x=>observed.get(x.table)!==x.count))throw Error("open complement mismatch");
const out=[
"From BusyCoq Require Import Agent5AutoTree.",
"From Coq Require Import List NArith Strings.String.",
"Import ListNotations.",
"Open Scope string_scope.",
"Open Scope nat_scope.",
"Definition auto_parent := TM_from_str \""+row.table+"\".",
"Definition auto_certificate : auto_tree := "+body+".",
"Definition auto_bound := "+root.bound+".",
"Lemma auto_checked : auto_check auto_bound auto_parent auto_certificate = true.",
"Proof. vm_compute. reflexivity. Qed.",
"Theorem auto_parent_safe : source_table_safe auto_bound auto_parent.",
"Proof. eapply auto_check_sound; exact auto_checked. Qed.",
"Print Assumptions auto_parent_safe."
].join("\n")+"\n";
fs.writeFileSync(process.argv[3]||"Agent5Q0AutoData.v",out);
console.log(JSON.stringify({rootId,table:row.table,n,bound:root.bound,open:observed.size}));
