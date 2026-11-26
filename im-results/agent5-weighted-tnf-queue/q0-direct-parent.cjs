"use strict";
const fs=require("node:fs"),path=require("node:path");
const {find,bank}=require("./coarse-pair.cjs");
const {mitmCert}=require("./q0-open-automata.cjs");
const {encodeCert}=require("./q0-direct-auto.cjs");
const moves=Array.from("ABCDEF").flatMap(q=>Array.from("01").flatMap(w=>Array.from("LR").map(d=>w+d+q)));
const rootId=Number(process.argv[2]);
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
 if(t[0]==="p"){let c=mitmCert(a.join(""),bank[t[1]],bank[t[2]]);if(!c)throw Error("MITM certificate failed");direct++;return "SATcert ("+encodeCert(c)+")";}
 if(t[0]==="s")return "SATw (SWside "+t[1]+" "+t[2]+" "+t[3]+" "+t[4]+")";
 if(t[0]!=="h")throw Error("unknown branch "+t[0]);
 if(!t[3].length)return "SATw (SWlast "+t[1]+")";
 if(t[3].length!==24)throw Error("incomplete first-hole split");
 return "source_auto_split "+t[1]+" ("+"ABCDEF"[t[2]>>1]+",S"+t[2]%2+") ["+t[3].map((kid,j)=>{let b=a.slice();b[t[2]]=moves[j];return encode(kid,b)}).join(";\n")+"]";
}
const body=encode(tree,row.table.replaceAll("_","").match(/.{3}/g));
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
fs.writeFileSync(process.argv[3]||"Agent5Q0AutoData.v",out);
console.log(JSON.stringify({rootId,table:row.table,n,bound:root.bound,open:observed.size,direct}));
