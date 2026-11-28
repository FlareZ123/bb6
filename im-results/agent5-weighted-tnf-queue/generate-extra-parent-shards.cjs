'use strict';
// Disjoint child proof modules; exact parent composition via sameTable_sound.
const fs=require('node:fs'),path=require('node:path'),adapter='../agent47-raw11-adapter/';
const {search}=require(adapter+'generate-raw11-extra.cjs');
const {searchPeriodic}=require('./q0-open-automata.cjs');
const {table,head,cert,slot,bit}=require(adapter+'generate-q0-lean.cjs');
const {sourceMitmCert}=require('./q0-source-mitm-cert.cjs');
const {bank}=require('./coarse-pair.cjs');
const route=require(adapter+'raw11-route.json');
const norm=s=>s.replaceAll('_',''),parse=s=>norm(s).match(/.{3}/g);
const moves=Array.from('ABCDEF').flatMap(q=>Array.from('01').flatMap(w=>Array.from('LR').map(d=>w+d+q)));
const move=j=>`⟨${bit(j%4>>1)},${bit(j%2)},${j>>2}⟩`;
const split=(t,a,f)=>t[3].map((k,j)=>[k,a.map((s,i)=>i===t[2]?moves[j]:s),Math.max(f,1+(j>>2))]);
const ext=new Map();
for(const id of [126,127]){
 const note=fs.readFileSync(path.join(__dirname,`raw11-extra-${id}.md`),'utf8');
 const rows=[...note.matchAll(/^\|\s*(\d+)\s*\|\s*`([01LRABCDEF_\-]+)`/gm)];
 if(rows.length!==(id===126?14:3))throw Error('symbolic roster '+id);
 for(const [,v,t] of rows)ext.set(norm(t),{module:`Raw11Extra${id}Coverage`,table:`Raw11Extra${id}Coverage.table ${v}`,proof:`Raw11Extra${id}Coverage.weighted ${v}`});
}
ext.set('1RB1RD1RC0RC0LA0RE1LA1LD0RD0RF---1LC',{module:'Raw11Extra137Coverage',table:'Raw11Extra137Coverage.table',proof:'Raw11Extra137Coverage.weighted'});
const known=new Map();
function add(c){if(known.has(c.table))throw Error('duplicate automaton '+c.table);known.set(c.table,c)}
for(const f of ['raw11-capped-extra-automata.json','raw11-capped-extra-automata-more.json'])for(const x of require('./'+f))add(x.result);
add(require('./raw11-capped-extra140-last-automata.json'));
for(const x of require('./raw11-six-hole-131-133.json').certs)add(x.result);
add(require('./raw11-six-hole-131-last-automata.json'));
if(process.env.SIX_HOLE_DATA)for(const f of fs.readdirSync(process.env.SIX_HOLE_DATA).filter(f=>/^six-hole-scan-\d+\.json$/.test(f)))for(const row of JSON.parse(fs.readFileSync(path.join(process.env.SIX_HOLE_DATA,f),'utf8')).rows)for(const x of row.certs)if(!known.has(x.cert.table))add(x.cert);
const id=Number(process.argv[2]),outdir=process.argv[3];
if(!Number.isInteger(id)||!route.extra[id]||!outdir)throw Error('usage: id outputdir');
fs.mkdirSync(outdir,{recursive:true});
const r=search(route.extra[id],{retain:true,cap:400000});
if(!r.tree)throw Error('incomplete '+id);
const B=r.bound,a=parse(r.table),f=Math.max(...a.filter(x=>x!=='---').map(x=>x.charCodeAt(2)-64));
const extendedAutomata=[];
if(process.env.RAW11_EXTENDED_AUTOMATA==='1'){
 for(const t of r.opens){
  const k=norm(t);
  if(!ext.has(k)&&!known.has(k)){
   const c=searchPeriodic(k);
   if(c){known.set(k,c);extendedAutomata.push({table:k,k:c.k,kind:c.kind,mirror:c.mirror,cap:c.cap,depth:c.depth,rows:c.rows?.length});}
  }
 }
}
const unresolved=r.opens.filter(t=>!ext.has(norm(t))&&!known.has(norm(t)));
if(unresolved.length)throw Error('unresolved '+JSON.stringify(unresolved));
const census=new WeakMap(),external=new WeakMap();
function count(t){let n=1,x=t[0]==='u'&&ext.has(t[1]);if(t[0]==='h')for(const k of t[3]){n+=count(k);x=x||external.get(k)}census.set(t,n);external.set(t,x);return n}
if(count(r.tree)!==r.n)throw Error('tree count');
const prefix='Agent5Raw11Extra'+id,modules=[];
const header=imports=>[...new Set(['PhaseTree','PhaseFrontier',...imports])].map(x=>'import '+x).join('\n')+'\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n';
const ns=n=>`namespace BB6.${n}\nopen BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree\n`;
function emit(t,a,f){switch(t[0]){
 case 's':return `(.side ${t[2]} ${t[3]} ${bit(t[1]==='R')} (${head(a,t[2])+(t[1]==='R'?-t[4]:t[4])}))`;
 case 'p':case 'o':case 'u':{const c=t[0]==='p'?sourceMitmCert(a.join(''),bank[t[1]],bank[t[2]]):t[0]==='o'?r.openBank[a.join('')]:known.get(a.join(''));if(!c||c.table!==a.join(''))throw Error('exact cert missing '+a.join(''));return `(.automata ${cert(c)})`}
 case 'h':return t[3].length?`(split ${t[1]} ${slot(t[2])} ${f} #[\n${split(t,a,f).map(k=>emit(...k)).join(',\n')}])`:`(.last ${t[1]} ${slot(t[2])})`;
 default:throw Error('bad node');
}}
const eq=(p,q)=>`have hEq : ${p} = ${q} := BB6.Agent47PhaseFrontier.sameTable_sound (by decide +kernel)\n  rw [hEq] at hm\n`;
function branch(t,f,p,safe,children){return `theorem ${safe} : ∀ m, compatible ${p} m → WeightedBound ${B} m := by
  apply split_safe ${B} ${p} ${t[1]} ${slot(t[2])} ${f} (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  have hcut : q.val ≤ ${f} := by simpa using h
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | ${children.map(n=>'exact '+n).join(' | ')} | omega
`}
function write(name,s){fs.writeFileSync(path.join(outdir,name+'.lean'),s);modules.push(name)}
const MODULE_SPLIT_THRESHOLD=1000;
function local(t,a,f,p,name,lines,imports,allowSplit=false){
 const safe='safe'+name;
 const repair = (process.env.RAW11_REPAIR_SPLIT==='1' &&
   ((id===132 && name.startsWith('_root_12_root_19')) ||
    (id===140 && name.startsWith('_root_6'))));
 const threshold = repair ? 30 : MODULE_SPLIT_THRESHOLD;
 const configuredCertThreshold = Number(process.env.RAW11_REPAIR_CERT_THRESHOLD || 8);
 if(!Number.isInteger(configuredCertThreshold) || configuredCertThreshold < 1)
   throw Error('bad RAW11_REPAIR_CERT_THRESHOLD');
 const certThreshold = repair ? configuredCertThreshold : 49;
 if(allowSplit&&census.get(t)>threshold){
  const moduleName=prefix+'Sub'+name.replace(/[^A-Za-z0-9_]/g,'_');
  const subLines=[ns(moduleName),parent(a)];
  const subImports=new Set();
  const subSafe=local(t,a,f,'parent',name+'_root',subLines,subImports,false);
  subLines.push(`theorem safe : ∀ m, compatible parent m → WeightedBound ${B} m := ${subSafe}
#print axioms safe
end BB6.${moduleName}
`);
  write(moduleName,header([...subImports])+subLines.join('\n'));
  imports.add(moduleName);
  lines.push(`theorem ${safe} : ∀ m, compatible ${p} m → WeightedBound ${B} m := by
  intro m hm
  ${eq(p,'BB6.'+moduleName+'.parent')}  exact BB6.${moduleName}.safe m hm
`);
  return safe;
 }
 if(t[0]==='u'&&ext.has(t[1])){const e=ext.get(t[1]);imports.add(e.module);lines.push(`theorem ${safe} : ∀ m, compatible ${p} m → WeightedBound ${B} m := by
   intro m hm
   ${eq(p,e.table)}  exact Cover.sound (${e.proof} ${B}) m hm
 `);return safe}
 if(census.get(t)<=certThreshold&&!external.get(t)){const c='cert'+name,h='checked'+name;lines.push(`def ${c} : Tree := ${emit(t,a,f)}
 theorem ${h} : check ${B} ${p} ${c} = true := by decide +kernel
 theorem ${safe} : ∀ m, compatible ${p} m → WeightedBound ${B} m := sound ${B} _ ${c} (by decide) ${h}
 `);return safe}
 if(t[0]!=='h'||!t[3].length)throw Error('not split');
 const names=[];
 for(const [j,[k,b,g]] of split(t,a,f).entries()){const n=name+'_'+j,q='p'+n;lines.push(`def ${q} := refine ${p} ${slot(t[2])} (some ${move(j)})\n`);names.push(local(k,b,g,q,n,lines,imports,true))}
 lines.push(branch(t,f,p,safe,names));return safe;
}
const parent=t=>`def parent : PartialMachine := ${table(t)}\n`;
if(r.tree[0]!=='h'||!r.tree[3].length)throw Error('unexpected root');
const names=[];
for(const [j,[k,b,g]] of split(r.tree,a,f).entries()){
 const name=prefix+'Kid'+String(j).padStart(2,'0'),imports=new Set(),lines=[ns(name),parent(b)];
 const safe=local(k,b,g,'parent','_root_'+j,lines,imports,true);
 lines.push(`theorem safe : ∀ m, compatible parent m → WeightedBound ${B} m := ${safe}\n#print axioms safe\nend BB6.${name}\n`);
 write(name,header([...imports])+lines.join('\n'));names.push(name)
}
const lines=[ns(prefix),parent(a)];
for(const [j,name] of names.entries()){
 const p=`refine parent ${slot(r.tree[2])} (some ${move(j)})`,q='BB6.'+name+'.parent';
 lines.push(`theorem child${j} : ∀ m, compatible (${p}) m → WeightedBound ${B} m := by
  intro m hm
  ${eq('('+p+')',q)}  exact BB6.${name}.safe m hm
`)
}
lines.push(branch(r.tree,f,'parent','safe',names.map((_,j)=>'child'+j)));
lines.push(`theorem cover : Cover (WeightedBound ${B}) parent := .leaf _ safe\n#print axioms cover\nend BB6.${prefix}\n`);
write(prefix,header(names)+lines.join('\n'));
fs.writeFileSync(path.join(outdir,'manifest.json'),JSON.stringify({id,table:r.table,nodes:r.n,bound:B,stats:r.stats,opens:r.opens,extendedAutomata,modules},null,2)+'\n');
console.log(JSON.stringify({id,nodes:r.n,bound:B,opens:r.opens.length,modules:modules.length}));
