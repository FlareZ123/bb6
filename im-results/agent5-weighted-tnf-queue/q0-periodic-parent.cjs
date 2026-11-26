'use strict';
// Complete first-hole trees for the four q0 source roots with D1 -> E.
// Search is untrusted. Emitted source_auto_check propositions are verified
// in the original BusyCoq semantics; every branch includes all 24 moves.
const fs=require('node:fs'),path=require('node:path');
const {classify,bank:historicalBank,mitmPair}=require('./coarse-pair.cjs');
const {searchPeriodic,mitmCert}=require('./q0-open-automata.cjs');
const {encodeCert}=require('./q0-direct-auto.cjs');
const moves=Array.from('ABCDEF').flatMap(q=>Array.from('01').flatMap(w=>Array.from('LR').map(d=>w+d+q)));
const configs={
 55:['0LE',601969,243,1697],
 56:['0RE',360361,71,12333],
 57:['1LE',873793,668,1547],
 58:['1RE',405841,185,656],
};
// Historical run DFA builder had initial id "" rather than JSON "[]".
// Keep its first five prefix DFAs, but use canonical empty state for run DFAs.
// Explicit direct certificates are emitted, never index the old Coq bank.
function runDFA(cap,mod,depth){
 const states=[[]],ids=new Map([['[]',0]]),dfa=[];
 for(let j=0;j<states.length;j++) {
  const old=states[j];
  dfa.push([0,1].map(b=>{
   let s;if(!old.length&&!b)s=[];
   else if(old.length&&old[0][0]===b)s=[[b,Math.min(cap,old[0][1]+1),(old[0][2]+1)%mod],...old.slice(1)];
   else s=[[b,1,1%mod],...old.slice(0,depth-1)];
   const k=JSON.stringify(s);if(!ids.has(k)){ids.set(k,states.length);states.push(s);}return ids.get(k);
  }));
 }
 return dfa;
}
const bank=historicalBank.slice(0,5);
for(const args of [[1,2,1],[1,3,1],[1,4,1],[2,2,1],[2,3,1],[3,1,1],[2,1,2],[3,1,2],[1,2,2],[1,3,2],[2,2,2],[1,4,2],[1,2,3],[2,1,3],[3,2,1],[1,5,1],[1,6,1]])bank.push(runDFA(...args));
const pairs=bank.map((_,i)=>[i,i]);
for(let i=0;i<bank.length;i++)for(let j=0;j<bank.length;j++)if(i!==j)pairs.push([i,j]);
pairs.sort((a,b)=>bank[a[0]].length*bank[a[1]].length-bank[b[0]].length*bank[b[1]].length);
function total(s){
 const n=s.push.length;
 return [...s.push.map(([x,y],i)=>[x,y].map((j,b)=>s.pop[j].some(([a,k])=>a===b&&k===i)?j:n)),[n,n]];
}
function simulate(a,limit){
 const tape=new Uint8Array(2*limit+5);let h=limit+2,q=0;
 for(let n=0;n<=limit;n++){const i=2*q+tape[h],tr=a[i];if(tr==='---')return {kind:'split',n,i};tape[h]=+tr[0];h+=tr[1]==='R'?1:-1;q=tr.charCodeAt(2)-65;}
 return {kind:'open'};
}
function scan(rootId) {
 const config=configs[rootId];if(!config)throw Error('unknown root '+rootId);
 const root=require('./q0-export/pilot-0-100-fuel-1000000.json').active[rootId];
 const table='1RB1RD_1RC---_0LA---_1LA'+config[0]+'_------_------';
 if(root.table!==table||root.holes!==6||root.fresh!==5)throw Error('wrong checkpoint identity');
 const stats={nodes:0,side:0,coarse:0,split:0,last:0,initialOpen:0,far:0,longTrace:0,maxHalt:0,kinds:{}};
 const certs={},traces={};
 function visit(a,h){
  stats.nodes++;
  let c=classify(a,256);
  if(c.kind==='open'){
   for(const [l,r] of pairs)if(mitmPair(a,bank[l],bank[r])){stats.coarse++;return ['p',l,r];}
   c=classify(a,1500);
   if(c.kind==='open'){
    stats.initialOpen++;const t=a.join('');
    const cert=searchPeriodic(t);
    if(cert){
     if(!mitmPair(a,total(cert.left),total(cert.right)))throw Error('independent totalization failed '+t);
     if(certs[t])throw Error('duplicate FAR leaf');
     certs[t]=cert;stats.far++;stats.kinds[cert.kind]=(stats.kinds[cert.kind]||0)+1;
     return ['a',t];
    }
    c=simulate(a,1000000);
    if(c.kind!=='split')throw Error('unresolved '+t);
    if(h!==1)throw Error('unexpected long nonfinal split '+t);
    stats.longTrace++;traces[t]=c;
   }
  }
  if(c.kind==='side'){stats.side++;return ['s',c.d,c.e,c.p,c.k];}
  if(c.kind!=='split'||a[c.i]!=='---')throw Error('wrong first hole');
  stats.maxHalt=Math.max(stats.maxHalt,c.n);
  if(h===1){stats.last++;return ['h',c.n,c.i,[]];}
  stats.split++;
  return ['h',c.n,c.i,moves.map(m=>{const b=a.slice();b[c.i]=m;return visit(b,h-1);})];
 }
 const tree=visit(table.replaceAll('_','').match(/.{3}/g),6);
 const bound=stats.maxHalt+6;
 if(stats.nodes!==config[1]||stats.initialOpen!==config[2]||bound!==config[3]||
    stats.nodes!==1+24*stats.split||stats.nodes!==stats.side+stats.coarse+stats.split+stats.last+stats.far||
    stats.initialOpen!==stats.far+stats.longTrace)throw Error('partition mismatch '+JSON.stringify(stats));
 return {rootId,table,bound,stats,tree,certs,traces};
}
const slot=i=>'('+'ABCDEF'[i>>1]+',S'+(i%2)+')';
const move=m=>'(S'+m[0]+','+m[1]+','+m[2]+')';
const header='From BusyCoq Require Import Agent5SourceAutoTree.\nFrom Coq Require Import List NArith Strings.String Lia.\nImport ListNotations.\nOpen Scope string_scope.\nOpen Scope nat_scope.\n';
function writeCoq(data,output){
 const {rootId,table,bound,tree,certs}=data;
 const dir=path.dirname(output),prefix='Agent5Q0Periodic'+rootId,defs=prefix+'Defs';
 const write=(n,s)=>fs.writeFileSync(path.join(dir,n+'.v'),s);
 write(defs,header+'Definition auto_parent := TM_from_str "'+table+'".\nDefinition auto_bound := '+bound+'.\n');
 const sizes=new WeakMap();
 function size(t){if(!sizes.has(t))sizes.set(t,1+(t[0]==='h'?t[3].reduce((s,k)=>s+size(k),0):0));return sizes.get(t);}
 function children(t,a){if(t[0]!=='h'||t[3].length!==24||a[t[2]]!=='---')throw Error('bad split');return t[3].map((kid,j)=>{const b=a.slice();b[t[2]]=moves[j];return [kid,b];});}
 function emit(t,a){
  switch(t[0]){
   case 's':return 'SATw (SWside '+t.slice(1).join(' ')+')';
   case 'p':{const c=mitmCert(a.join(''),bank[t[1]],bank[t[2]]);if(!c)throw Error('coarse cert failed');return 'SATcert ('+encodeCert(c)+')';}
   case 'a':{if(t[1]!==a.join(''))throw Error('FAR table mismatch');return 'SATcert ('+encodeCert(certs[t[1]])+')';}
   case 'h':return t[3].length?'source_auto_split '+t[1]+' '+slot(t[2])+' ['+children(t,a).map(([k,b])=>emit(k,b)).join(';\n')+']':'SATw (SWlast '+t[1]+')';
   default:throw Error('unknown node');
  }
 }
 function assemble(n,p,t,kids){
  return 'Theorem safe_'+n+' : source_table_safe auto_bound '+p+'.\nProof.\n  eapply source_first_hole_split with (n:='+t[1]+') (h:='+slot(t[2])+').\n  - apply source_hole_atb_sound. vm_compute. reflexivity.\n  - unfold auto_bound. lia.\n  - intros [[s d] q]. destruct q; destruct s; destruct d; first ['+kids.map(k=>'exact safe_'+k).join(' | ')+'].\nQed.\n';
 }
 function prove(n,p,t,a){
  if(size(t)<=400) return 'Definition cert_'+n+' : source_auto_tree := '+emit(t,a)+'.\nLemma check_'+n+' : source_auto_check auto_bound '+p+' cert_'+n+' = true.\nProof. vm_compute. reflexivity. Qed.\nTheorem safe_'+n+' : source_table_safe auto_bound '+p+'.\nProof. eapply source_auto_check_sound; exact check_'+n+'. Qed.\n';
  const kids=children(t,a),ns=kids.map((_,j)=>n+'_'+j);
  return kids.map(([k,b],j)=>'Definition p_'+ns[j]+' := tm_upd '+p+' '+slot(t[2])+' '+move(moves[j])+'.\n'+prove(ns[j],'p_'+ns[j],k,b)).join('')+assemble(n,p,t,ns);
 }
 const modules=[],leaves=[];
 // Each major child is split once more if large. Small modules allow
 // independent .vo reuse and prevent a single giant proof term.
 function shard(n,p,t,a,name,imports){
  if(size(t)<=12000){write(name,header+'From BusyCoq Require Import '+imports.join(' ')+'.\n'+prove(n,p,t,a)+'Print Assumptions safe_'+n+'.\n');leaves.push(name);return name;}
  const kids=children(t,a),ns=kids.map((_,j)=>n+'_'+j),base=name+'Base';
  write(base,header+'From BusyCoq Require Export '+imports.join(' ')+'.\n'+kids.map((_,j)=>'Definition p_'+ns[j]+' := tm_upd '+p+' '+slot(t[2])+' '+move(moves[j])+'.\n').join(''));
  const deps=kids.map(([k,b],j)=>shard(ns[j],'p_'+ns[j],k,b,name+'K'+String(j).padStart(2,'0'),[base]));
  write(name,header+'From BusyCoq Require Import '+base+' '+deps.join(' ')+'.\n'+assemble(n,p,t,ns));
  return name;
 }
 const a=table.replaceAll('_','').match(/.{3}/g),kids=children(tree,a),ns=kids.map((_,j)=>'r'+j);
 const top=prefix+'Top';
 write(top,header+'From BusyCoq Require Export '+defs+'.\n'+kids.map((_,j)=>'Definition p_'+ns[j]+' := tm_upd auto_parent '+slot(tree[2])+' '+move(moves[j])+'.\n').join(''));
 for(let j=0;j<24;j++)modules.push(shard(ns[j],'p_'+ns[j],kids[j][0],kids[j][1],prefix+'S'+String(j).padStart(2,'0'),[top]));
 fs.writeFileSync(output,header+'From BusyCoq Require Export '+defs+'.\nFrom BusyCoq Require Import '+top+' '+modules.join(' ')+'.\n'+assemble('root','auto_parent',tree,ns)+'Theorem auto_parent_safe : source_table_safe auto_bound auto_parent.\nProof. exact safe_root. Qed.\nPrint Assumptions auto_parent_safe.\n');
 return {modules,leaves};
}
function main(rootId,output){
 const d=scan(rootId);const manifest={rootId:d.rootId,table:d.table,bound:d.bound,stats:d.stats,traces:d.traces,far:Object.values(d.certs).map(c=>({table:c.table,k:c.k,kind:c.kind,mirror:c.mirror,cap:c.cap,depth:c.depth,rows:c.rows.length}))};
 if(output)Object.assign(manifest,writeCoq(d,output));
 console.log(JSON.stringify(manifest));
}
if(require.main===module)main(+process.argv[2],process.argv[3]);
module.exports={main,scan,bank,pairs};
