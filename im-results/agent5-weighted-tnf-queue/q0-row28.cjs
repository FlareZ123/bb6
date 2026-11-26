"use strict";
const fs=require("node:fs");
const path=require("node:path");
const {find,emit}=require("./coarse-pair.cjs");
const root="1RB1RD_1RC0RE_0LA1RF_1LA1LD_---0LA_------";
const solid="1RB1RD1RC0RE0LA1RF1LA1LD1LE0LA---0RE";
const data=JSON.parse(fs.readFileSync(path.join(__dirname,"q0-export/pilot-0-100-fuel-1000000.json"),"utf8"));
const row=data.active[28];
if(row.table!==root || row.holes!==3 || row.fresh!==6)throw Error("row 28 changed");
const {tree,n}=find(row,true);
if(!tree)throw Error("candidate search aborted");
const stats={side:0,mitm:0,last:0,split:0,open:0};
let maxHalt=0;
function scan(t){
  switch(t[0]){
    case "s":stats.side++;break;
    case "p":stats.mitm++;break;
    case "o":
      if(t[1]!==solid)throw Error("unexpected uncovered descendant: "+t[1]);
      stats.open++;break;
    case "h":
      maxHalt=Math.max(maxHalt,t[1]);
      if(t[3].length===0)stats.last++;
      else{
        if(t[3].length!==24)throw Error("incomplete split");
        stats.split++;t[3].forEach(scan);
      }
      break;
    default:throw Error("invalid node");
  }
}
scan(tree);
if(stats.open!==1)throw Error("expected exactly one symbolic leaf");
function containsSolid(t){return t[0]==="o" || (t[0]==="h" && t[3].some(containsSolid));}
function emitRoot(t){
  if(t[0]==="o")return "R28solid";
  if(!containsSolid(t))return "R28coarse ("+emit(t)+")";
  return "row28_split "+t[1]+" ("+"ABCDEF"[t[2]>>1]+",S"+(t[2]%2)+") ["+t[3].map(emitRoot).join(";\n")+"]";
}
const bound=maxHalt+6;
const lines=[
  "From BusyCoq Require Import Agent5Row28Tree.",
  "From Coq Require Import List Strings.String.",
  "Import ListNotations.",
  "Open Scope string_scope.",
  "Open Scope nat_scope.",
  'Definition row28_parent := TM_from_str "'+root+'".',
  "Definition row28_certificate : row28_tree := "+emitRoot(tree)+".",
  "Lemma row28_checked : row28_check "+bound+" row28_parent row28_certificate = true.",
  "Proof. vm_compute. reflexivity. Qed.",
  "Theorem row28_safe : source_table_safe "+bound+" row28_parent.",
  "Proof. eapply row28_check_sound; exact row28_checked. Qed.",
  "Print Assumptions row28_safe."
];
fs.writeFileSync(process.argv[2]||"Agent5Row28Data.v",lines.join("\n")+"\n");
console.log(JSON.stringify({root,n,bound,stats,maxHalt},null,2));
