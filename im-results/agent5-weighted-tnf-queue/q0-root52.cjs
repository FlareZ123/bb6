'use strict';
// Exhaustive original-direction q0 active root 52 candidate; no fresh-state quotient.
const fs=require('node:fs'),path=require('node:path');
const {classify,bank,pairs,mitmPair}=require('./coarse-pair.cjs');
const {search}=require('./q0-open-automata.cjs');
const moves=Array.from('ABCDEF').flatMap(q=>Array.from('01').flatMap(w=>Array.from('LR').map(d=>w+d+q)));
const data=require('./q0-export/pilot-0-100-fuel-1000000.json');
const root=data.active[52], expected='1RB1RD_1RC1LE_0LA---_1LA1LD_------_------';
if(root.table!==expected||root.holes!==5||root.fresh!==5)throw Error('wrong root');
const start=root.table.replaceAll('_','').match(/.{3}/g);
const target='1RB1RD1RC1LE0LA0RC1LA1LD---0LF1LB0LB';
const stats={nodes:0,side:0,coarse:0,split:0,last:0,far:0,long:0,maxHalt:0};
const far=[];
function total(s){const n=s.push.length;return [...s.push.map(([x,y],i)=>[x,y].map((j,b)=>s.pop[j].some(([a,k])=>a===b&&k===i)?j:n)),[n,n]];}
function visit(a,h){
  if(++stats.nodes>50000)throw Error('node budget');
  let c=classify(a,256);
  if(c.kind==='open'){
    for(const [l,r] of pairs)if(mitmPair(a,bank[l],bank[r])){stats.coarse++;return ['p',l,r];}
    c=classify(a,1500);
    if(c.kind==='open'){
      const table=a.join('');
      if(table===target){
        c=classify(a,5000);
        if(c.kind!=='split'||c.n!==4657||c.i!==8||h!==1)throw Error('long halt mismatch');
        stats.long++;
      }else{
        const cert=search(table);if(!cert)throw Error('unresolved '+table);
        const l=total(cert.left),r=total(cert.right);
        if(!mitmPair(a,l,r))throw Error('lifted certificate failed '+table);
        far.push({table,rows:cert.rows.length,left:l.length,right:r.length});stats.far++;
        return ['d',l,r];
      }
    }
  }
  if(c.kind==='side'){stats.side++;return ['s',c.d,c.e,c.p,c.k];}
  if(c.kind!=='split')throw Error('unclassified');
  stats.maxHalt=Math.max(stats.maxHalt,c.n);
  if(h===1){stats.last++;return ['h',c.n,c.i,[]];}
  stats.split++;
  return ['h',c.n,c.i,moves.map(m=>{const b=a.slice();b[c.i]=m;return visit(b,h-1);})];
}
const tree=visit(start,5);
const bound=stats.maxHalt+6;
if(stats.nodes!==27409||stats.far!==11||stats.long!==1||bound!==4663||stats.nodes!==stats.side+stats.coarse+stats.split+stats.last+stats.far)throw Error('unexpected candidate counts '+JSON.stringify(stats));
const slot=i=>'('+ 'ABCDEF'[i>>1]+',S'+(i%2)+')';
const move=m=>'(S'+m[0]+','+m[1]+','+m[2]+')';
const listN=x=>'['+x.flat().map(n=>n+'%N').join(';')+']';
function emit(t){switch(t[0]){
 case 's':return 'ATcoarse (CTw (SWside '+t.slice(1).join(' ')+'))';
 case 'p':return 'ATcoarse (CTpair '+t[1]+' '+t[2]+')';
 case 'd':return 'ATdfa '+listN(t[1])+' '+listN(t[2]);
 case 'h':return t[3].length?'auto_split '+t[1]+' '+slot(t[2])+' ['+t[3].map(emit).join(';\n')+']':'ATcoarse (CTw (SWlast '+t[1]+'))';
 default:throw Error('bad tree');}}
function size(t){return 1+(t[0]==='h'?t[3].reduce((s,k)=>s+size(k),0):0);}
const output=process.argv[3]||'Agent5Q0AutoData.v';
const dir=path.dirname(output), prefix='Agent5Q0Root52';
const hdr='From BusyCoq Require Import Agent5AutoTree.\nFrom Coq Require Import List NArith Strings.String Lia.\nImport ListNotations.\nOpen Scope string_scope.\nOpen Scope nat_scope.\n';
const defs=prefix+'Defs';
const write=(name,body)=>fs.writeFileSync(path.join(dir,name+'.v'),body);
write(defs,hdr+'Definition auto_parent := TM_from_str "'+root.table+'".\nDefinition auto_bound := '+bound+'.\n');
function assemble(n,p,t,kids){return 'Theorem safe_'+n+' : source_table_safe auto_bound '+p+'.\nProof.\n  eapply source_first_hole_split with (n:='+t[1]+') (h:='+slot(t[2])+').\n  - apply source_hole_atb_sound. vm_compute. reflexivity.\n  - unfold auto_bound. lia.\n  - intros [[s d] q]. destruct q; destruct s; destruct d; first ['+kids.map(k=>'exact safe_'+k).join(' | ')+'].\nQed.\n';}
function prove(n,p,t){
  if(size(t)<=400){return 'Definition cert_'+n+' : auto_tree := '+emit(t)+'.\nLemma check_'+n+' : auto_check auto_bound '+p+' cert_'+n+' = true.\nProof. vm_compute. reflexivity. Qed.\nTheorem safe_'+n+' : source_table_safe auto_bound '+p+'.\nProof. eapply auto_check_sound; exact check_'+n+'. Qed.\n';}
  if(t[0]!=='h'||t[3].length!==24)throw Error('invalid cut');
  const kids=t[3].map((_,j)=>n+'_'+j);
  let s='';for(let j=0;j<24;j++){const k=kids[j];s+='Definition p_'+k+' := tm_upd '+p+' '+slot(t[2])+' '+move(moves[j])+'.\n'+prove(k,'p_'+k,t[3][j]);}
  return s+assemble(n,p,t,kids);
}
if(tree[0]!=='h'||tree[3].length!==24)throw Error('invalid root split');
const modules=[],kids=[];
for(let j=0;j<24;j++){
 const name=prefix+'S'+String(j).padStart(2,'0'),n='r'+j,p='p_'+n;modules.push(name);kids.push(n);
 write(name,hdr+'From BusyCoq Require Import '+defs+'.\nDefinition '+p+' := tm_upd auto_parent '+slot(tree[2])+' '+move(moves[j])+'.\n'+prove(n,p,tree[3][j])+'Print Assumptions safe_'+n+'.\n');
}
fs.writeFileSync(output,hdr+'From BusyCoq Require Export '+defs+'.\nFrom BusyCoq Require Import '+modules.join(' ')+'.\n'+assemble('root','auto_parent',tree,kids)+'Theorem auto_parent_safe : source_table_safe auto_bound auto_parent.\nProof. exact safe_root. Qed.\nPrint Assumptions auto_parent_safe.\n');
console.log(JSON.stringify({rootId:52,table:root.table,bound,stats,far,modules}));
