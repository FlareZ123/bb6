"use strict";
// Reuse the direct source certificates, but check bounded subtrees
// separately and compose larger splits through source_first_hole_split.
const fs = require("node:fs"), path = require("node:path");
function emitShards({rootId,row,tree,bound,encode,moves,output,chunkCap=25,timed=false}) {
  const prefix="Agent5Q0Direct"+rootId, defs=prefix+"Defs", top=prefix+"Top";
  const dir=path.dirname(output);
  const header="From BusyCoq Require Import Agent5SourceAutoTree Enumerate62 Agent8WeightedSource.\n"+
    "From Coq Require Import List NArith Strings.String Lia.\n"+
    "Import ListNotations TNF_Node.\nOpen Scope string_scope.\nOpen Scope nat_scope.\n";
  const write=(n,s)=>fs.writeFileSync(path.join(dir,n+".v"),s);
  const slot=i=>"("+"ABCDEF"[i>>1]+",S"+(i%2)+")";
  const move=m=>"(S"+m[0]+","+m[1]+","+m[2]+")";
  const size=t=>1+(t[0]==="h"?t[3].reduce((s,k)=>s+size(k),0):0);
  const manifest={rootId,chunkCap,nodes:size(tree),chunks:0,maxChunk:0,splitProofs:0,shards:[]};
  function children(t,a) {
    if(t[0]!=="h"||t[3].length!==24||moves.length!==24||a[t[2]]!=="---")
      throw Error("incomplete first-hole split");
    return t[3].map((k,j)=>{const b=a.slice();b[t[2]]=moves[j];return [k,b];});
  }
  function definitions(n,p,t) {
    return moves.map((m,j)=>"Definition p_"+n+"_"+j+" := tm_upd "+p+" "+slot(t[2])+" "+move(m)+".\n").join("");
  }
  function assemble(n,p,t,ns) {
    manifest.splitProofs++;
    // The focused root-26 pilot avoids guessing certificate arguments and
    // makes the exact slow command visible. Every split has all 24 children.
    if(timed) return "Theorem safe_"+n+" : source_table_safe auto_bound "+p+".\n"+
      "Proof.\n  refine (@source_first_hole_split auto_bound "+p+" "+t[1]+" "+slot(t[2])+" _ _ _).\n"+
      "  - idtac \"hole "+n+"\". refine (@source_hole_atb_sound "+p+" "+t[1]+" "+slot(t[2])+" _). Time vm_compute. reflexivity.\n"+
      "  - unfold auto_bound. lia.\n"+
      "  - intros [[s d] q]. destruct q; destruct s; destruct d.\n"+
      ns.map(k=>"    + exact safe_"+k+".\n").join("")+
      "Time Qed.\n";
    return "Theorem safe_"+n+" : source_table_safe auto_bound "+p+".\n"+
      "Proof.\n  eapply source_first_hole_split with (n:="+t[1]+") (h:="+slot(t[2])+").\n"+
      "  - apply source_hole_atb_sound. vm_compute. reflexivity.\n"+
      "  - unfold auto_bound. lia.\n"+
      "  - intros [[s d] q]. destruct q; destruct s; destruct d; first ["+
      ns.map(k=>"exact safe_"+k).join(" | ")+"].\nQed.\n";
  }
  function prove(n,p,t,a) {
    const count=size(t);
    if(count<=chunkCap) {
      manifest.chunks++;
      manifest.maxChunk=Math.max(manifest.maxChunk,count);
      if(timed) return "Time Definition cert_"+n+" : source_auto_tree := "+encode(t,a)+".\n"+
        "Lemma check_"+n+" : source_auto_check auto_bound "+p+" cert_"+n+" = true.\n"+
        "Proof. idtac \"check "+n+"\". Time vm_compute. reflexivity. Time Qed.\n"+
        "Theorem safe_"+n+" : source_table_safe auto_bound "+p+".\n"+
        "Proof. exact (@source_auto_check_sound auto_bound "+p+" cert_"+n+" check_"+n+"). Time Qed.\n";
      return "Definition cert_"+n+" : source_auto_tree := "+encode(t,a)+".\n"+
        "Lemma check_"+n+" : source_auto_check auto_bound "+p+" cert_"+n+" = true.\n"+
        "Proof. vm_compute. reflexivity. Qed.\n"+
        "Theorem safe_"+n+" : source_table_safe auto_bound "+p+".\n"+
        "Proof. eapply source_auto_check_sound; exact check_"+n+". Qed.\n";
    }
    const kids=children(t,a),ns=kids.map((_,j)=>n+"_"+j);
    return definitions(n,p,t)+kids.map(([k,b],j)=>prove(ns[j],"p_"+ns[j],k,b)).join("")+assemble(n,p,t,ns);
  }
  write(defs,header+'Definition auto_parent := TM_from_str "'+row.table+'".\nDefinition auto_bound := '+bound+".\n");
  const a=row.table.replaceAll("_","").match(/.{3}/g),kids=children(tree,a),ns=kids.map((_,j)=>"r_"+j);
  write(top,header+"From BusyCoq Require Export "+defs+".\n"+definitions("r","auto_parent",tree));
  const modules=kids.map(([k,b],j)=>{
    const name=prefix+"S"+String(j).padStart(2,"0"),before=manifest.chunks;
    write(name,header+"From BusyCoq Require Import "+top+".\n"+
      prove(ns[j],"p_"+ns[j],k,b)+"Print Assumptions safe_"+ns[j]+".\n");
    manifest.shards.push({name,move:moves[j],nodes:size(k),chunks:manifest.chunks-before});
    return name;
  });
  fs.writeFileSync(output,header+"From BusyCoq Require Export "+defs+".\n"+
    "From BusyCoq Require Import "+top+" "+modules.join(" ")+".\n"+
    assemble("root","auto_parent",tree,ns)+
    "Theorem auto_parent_safe : source_table_safe auto_bound auto_parent.\n"+
    "Proof. exact safe_root. Qed.\nPrint Assumptions auto_parent_safe.\n");
  return manifest;
}
module.exports={emitShards};
