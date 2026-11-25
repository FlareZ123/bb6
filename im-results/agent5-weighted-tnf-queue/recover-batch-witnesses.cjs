#!/usr/bin/env node
"use strict";
const fs = require("node:fs");
const path = require("node:path");
const MOVES = [..."ABCDEF"].flatMap(q => [..."01"].flatMap(w => [..."LR"].map(d => w+d+q)));
const PIN = "33209bc7dc282b38c8cd6be507bfc551fea56108";

/** @param {string} table @returns {string[]} */
function slots(table) { return table.replaceAll("_", "").match(/.{3}/g); }
/** @param {string[]} actions @returns {string} */
function tableOf(actions) { return actions.filter((_,i)=>i%2===0).map((a,i)=>a+actions[2*i+1]).join("_"); }
/** @param {Set<number>} tape @param {number} head @param {number} direction @param {number} k */
function retained(tape,head,direction,k) {
  return [...tape].map(x=>(x-head)*direction).filter(x=>x>=-k).sort((a,b)=>a-b).join(",");
}
/** @param {string} table @param {number} limit */
function classify(table,limit=80) {
  const a=slots(table), histories=Array.from({length:6},()=>[]), heads=[];
  const tape=new Set(); let q=0,head=0;
  for(let n=0;n<=limit;n++){
    heads.push(head);
    for(let j=histories[q].length-1;j>=0;j--){
      const [entry,h,t]=histories[q][j], d=head>=h?1:-1;
      let k=0;for(let i=entry;i<=n;i++)k=Math.max(k,(h-heads[i])*d);
      if(retained(t,h,d,k)===retained(tape,head,d,k))
        return {kind:"side",d:d===1?"R":"L",entry,period:n-entry,k};
    }
    histories[q].push([n,head,new Set(tape)]);
    const slot=2*q+Number(tape.has(head)), tr=a[slot];
    if(tr==="---")return {kind:a.filter(x=>x==="---").length===1?"last":"split",n,slot};
    if(tr[0]==="1")tape.add(head);else tape.delete(head);
    head+=tr[1]==="R"?1:-1;q=tr.charCodeAt(2)-65;
  }
  return {kind:"open"};
}
/** @param {string} table */
function checkedTable(table){
  if(!/^(?:(?:[01][LR][A-F]|---){2}_){5}(?:[01][LR][A-F]|---){2}$/.test(table))
    throw Error("bad table: "+table);
  return table;
}
/** @param {string} dir */
function manifestPaths(dir) {
  return fs.readdirSync(dir,{withFileTypes:true}).flatMap(e=>{
    const p=path.join(dir,e.name);return e.isDirectory()?manifestPaths(p):e.name==="manifest.tsv"?[p]:[];
  });
}
/** @param {string} dir */
function recover(dir) {
  const chosen=new Map();
  for(const m of manifestPaths(dir)){
    const root=path.dirname(m);
    if(fs.readFileSync(path.join(root,"original-revision.txt"),"utf8").trim()!==PIN)throw Error("source revision mismatch");
    const rows=fs.readFileSync(m,"utf8").trim().split(/\r?\n/);
    if(rows.shift()!=="offset\tsize\tfuel\tstatus")throw Error("bad manifest");
    for(const row of rows){
      const [offset,size,fuel,status]=row.split("\t");
      if(status!=="verified")continue;
      const name=["Agent8Batch",offset,size,fuel].join("_");
      if(!fs.existsSync(path.join(root,name+".vo")))throw Error("missing compiled proof: "+name);
      const log=fs.readFileSync(path.join(root,name+".log"),"utf8");
      const counts=[...log.matchAll(/=\s*\((\d+),\s*(\d+)\)/g)].at(-1);
      const packed=log.split("chunk_data =").at(-1).split(/\n\s*:/)[0];
      const lists=packed.split(/\]\s*,\s*\[/);
      if(!counts||lists.length!==2)throw Error("missing packed data: "+name);
      const nodes=lists.map(s=>[...s.matchAll(/\("([01LRABCDEF_-]+)",\s*(\d+),\s*(\d+)\)/g)].map(x=>checkedTable(x[1])));
      if(nodes[0].length!==Number(counts[1])||nodes[1].length!==Number(counts[2]))throw Error("count mismatch "+name);
      const old=chosen.get(Number(offset));
      if(old&&old.fuel===Number(fuel)&&JSON.stringify(old.nodes)!==JSON.stringify(nodes))throw Error("conflicting equal-fuel outputs: "+name);
      if(!old||old.fuel<Number(fuel))chosen.set(Number(offset),{fuel:Number(fuel),nodes});
    }
  }
  return [...chosen].sort((a,b)=>a[0]-b[0]);
}
/** @param {ReturnType<typeof classify>} w */
function cert(w){
  if(w.kind==="side")return "STcert (SWside "+[w.d,w.entry,w.period,w.k].join(" ")+")";
  if(w.kind==="last")return "STcert (SWlast "+w.n+")";
  return null;
}
/** @param {string} table */
function discoverTree(table){
  const w=classify(table), c=cert(w);if(c)return {code:c,kind:w.kind};
  if(w.kind!=="split")return null;
  const actions=slots(table);
  const children=MOVES.map(m=>{const a=actions.slice();a[w.slot]=m;return cert(classify(tableOf(a)));});
  if(children.some(x=>!x))return null;
  const q="ABCDEF"[Math.floor(w.slot/2)], s="S"+(w.slot%2);
  return {code:"source_split "+w.n+" ("+q+","+s+") ["+children.join("; ")+"]",kind:"closedSplit"};
}
/** @param {string[]} tables */
function generate(tables) {
  const candidates=[], stats={side:0,last:0,closedSplit:0,open:0};
  for(const table of new Set(tables)){
    const t=discoverTree(checkedTable(table));
    if(!t){stats.open++;continue;}
    stats[t.kind]++;candidates.push('("'+table+'", '+t.code+')');
  }
  const body=candidates.join(";\n  ");
  console.error(JSON.stringify(stats));
  return 'From BusyCoq Require Import Agent47SourceTree Agent47SourceWitness SourceResidualRoster Individual62.\n'+
'From Coq Require Import List Bool Strings.String Lia.\nImport ListNotations.\nOpen Scope string_scope.\nOpen Scope nat_scope.\n'+
'Definition recovered_trees : list (string * source_tree) := [\n  '+body+'\n].\n'+
'Definition recovered_check (b : nat) (c : string * source_tree) : bool :=\n'+
'  let (s,t) := c in source_tree_check b (TM_from_str s) t &&\n'+
'    match source_tree_open (TM_from_str s) t with [] => true | _ => false end.\n'+
'Lemma recovered_check_sound b c : recovered_check b c = true -> source_table_safe b (TM_from_str (fst c)).\n'+
'Proof.\n  destruct c as [s t]. cbn [recovered_check fst].\n'+
'  rewrite andb_true_iff. intros [HC HO].\n'+
'  apply (source_tree_sound b (TM_from_str s) t HC).\n'+
'  destruct (source_tree_open (TM_from_str s) t); [constructor|discriminate].\nQed.\n'+
'Definition recovered_roster := map (fun c => TM_from_str (fst c)) recovered_trees.\n'+
'Theorem recovered_checked : forallb (recovered_check 1000006) recovered_trees = true.\n'+
'Proof. vm_compute. reflexivity. Qed.\n'+
'Theorem recovered_roster_safe : Forall (source_table_safe 1000006) recovered_roster.\n'+
'Proof.\n  apply Forall_forall. intros p Hp. unfold recovered_roster in Hp.\n'+
'  apply in_map_iff in Hp. destruct Hp as [c [E HIn]]. subst p.\n'+
'  apply recovered_check_sound. eapply forallb_forall; [exact recovered_checked|exact HIn].\nQed.\n'+
'Print Assumptions recovered_roster_safe.\n';
}
if(require.main===module){
  const [input,output]=process.argv.slice(2);
  if(!input||!output)throw Error("usage: node recover-batch-witnesses.cjs extracted-batch-root|tables.txt output.v");
  let tables;
  if(fs.statSync(input).isDirectory()){
    const chunks=recover(input);
    tables=chunks.flatMap(([,c])=>c.nodes.flat());
    console.error("verified chunk offsets: "+chunks.map(([i])=>i).join(",")+"; nodes "+tables.length);
  }else tables=fs.readFileSync(input,"utf8").trim().split(/\r?\n/).map(l=>l.trim().split(/\s+/).at(-1));
  fs.writeFileSync(output,generate(tables));
}
module.exports={classify,discoverTree,recover,generate};
