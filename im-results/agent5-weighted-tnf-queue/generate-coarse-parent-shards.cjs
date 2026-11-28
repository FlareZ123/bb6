'use strict';
// Generate sharded original-source Lean proofs from the exact retained normalized tree.
// Discovery trees are untrusted: every ordinary chunk is checked by Lean's kernel;
// external leaves use exact table equality and independently established covers.
const fs=require('node:fs'),path=require('node:path');
const {moves,bank,sourceMitmCert}=require('./scan-q0-coarse-full.cjs');
const {table,cert,slot,bit}=require('../agent47-raw11-adapter/generate-q0-lean.cjs');
const {search,searchPeriodic}=require('./q0-open-automata.cjs');
const pumpNS='BB6Coverage.Agent31Pump.Auto.Raw11Q0Coarse';
const parse=s=>s.replaceAll('_','').match(/.{3}/g), norm=s=>s.replaceAll('_','');
const move=j=>`⟨${bit(j%4>>1)},${bit(j%2)},${j>>2}⟩`;
const fill=(a,i,j)=>a.map((t,k)=>i===k?moves[j]:t);
const fresh=a=>Math.max(...a.filter(x=>x!=='---').map(x=>x.charCodeAt(2)-64),...a.map((x,i)=>x==='---'?0:1+(i>>1)));
const id=Number(process.argv[2]),input=process.argv[3],output=process.argv[4],CHUNK=Number(process.argv[5]||400),MOD=Number(process.argv[6]||6000);
if(!Number.isSafeInteger(id)||id<0||!input||!output||!Number.isSafeInteger(CHUNK)||CHUNK<25||!Number.isSafeInteger(MOD)||MOD<CHUNK)throw Error('usage: id scan-artifact-dir outputdir [chunk=400] [module=6000]');
fs.mkdirSync(output,{recursive:true});
const summary=JSON.parse(fs.readFileSync(path.join(input,'summary.json'),'utf8')),tree=JSON.parse(fs.readFileSync(path.join(input,'tree.json'),'utf8'));
const route=require('../agent47-raw11-adapter/raw11-route.json');
if(summary.id!==id||summary.table!==route.targets[id])throw Error('wrong root artifact');
const pumps=new Map(require('./q0-coarse-pumps.json').map(c=>[c.root,c.table]));
const longMap=new Map(require('./q0-coarse-long-holes.json').map(c=>[norm(c.table),c]));
// Each external cut is matched by its entire 12-entry table; no index/count substitution.
// Importing the actual theorem is mandatory even when the source proof is still pending CI.
const regionCuts=new Map([
 ['1RB1LC1RC0LF0LA0RD1RA1RE1LF1RD---0LB', {root:149,mod:'Q0149H11',ns:'BB6.Agent50Q0149H11',tableField:'ctr'}],
 ['1RB1LC1RC---0LA0RD1RA1RE1LF1RD1LC0LF', {root:149,mod:'Q0149H16',ns:'BB6.Agent50Q0149H16',tableField:'ctr'}],
 ['1RB1LC1RC---0LA0RD1RA1RE1LF1RD1RC0LF', {root:149,mod:'Q0149H17',ns:'BB6.Agent50Q0149H17',tableField:'ctr'}],
 ['1RB1LC1RC0LC0LA0RD1RF1RE0RB---1LB1RE', {root:149,mod:'Q0149Block8',ns:'BB6.Agent50Q0149Block8'}],
 ['1RB1LC1RC0RC0LA0RD1RB1RE0RF---1LC0LC', {root:149,mod:'Q0149Block10',ns:'BB6.Agent50Q0149Block10'}],
 ['1RB1LC1RC---0LA0RD1RF1RE0RD0RB1LA0LC', {root:149,mod:'Raw11Q0LongSweep2',ns:'BB6.Raw11Q0LongSweep2',minBound:195836}],
 ['1RB1LC1RC1RF0LA1LD0LE0RB1LA---1RA0LA', {root:150,mod:'Raw11Q0LongSweep0',ns:'BB6.Raw11Q0LongSweep0',minBound:1102626}],
 ['1RB1LC1RC1RF0LA1LD0LB0RE0LC1RD1RA---', {root:150,mod:'Raw11Q0LongSweep1',ns:'BB6.Raw11Q0LongSweep1',minBound:13007752}],
 ['1RB1LC1RC1RF0LA1LD1LE0RB0LA---1RA0LA', {root:150,mod:'Raw11Q0LongSweep3',ns:'BB6.Raw11Q0LongSweep3',minBound:1102614}],
 ['1RB1LC1RC1RF0LA1LD1LE0RB0RA---1RA0LA', {root:150,mod:'Raw11Q0LongSweep4',ns:'BB6.Raw11Q0LongSweep4',minBound:1102626}],
 ['1RB1LC1RC1RF0LA1LD1LE0RB0LB---1RA0LA', {root:150,mod:'Raw11Q0LongSweep5',ns:'BB6.Raw11Q0LongSweep5',minBound:2625204}],
 ['1RB1LC1RC0RE0LA1LD1LA1RE---0RF1LC1RD', {root:150,mod:'Raw11Q0Double150',ns:'BB6Coverage.Agent31Pump.Raw11Q0Double150'}],
 ['1RB1LC1RC0RE0LA1LD0RB1LC---1RF0LA1RB', {root:150,mod:'Raw11Q0Frame150Rules',ns:'BB6Coverage.Agent31Pump.Frame150.Raw11.M0'}],
 ['1RB1LC1RC0RE0LA1LD0RB1LC---1RF0LD1RB', {root:150,mod:'Raw11Q0Frame150Rules',ns:'BB6Coverage.Agent31Pump.Frame150.Raw11.M1'}],
 ['1RB1LC1RC0RE0LA1LD0RB1LC---1RF0RD1RB', {root:150,mod:'Raw11Q0Frame150Rules',ns:'BB6Coverage.Agent31Pump.Frame150.Raw11.M2'}],
 ['1RB1LC1RC---0LA1RD0RE1LD1RA0RF0RC0LB', {root:151,mod:'Raw11Q0Linear151',ns:'BB6Coverage.Agent31Pump.Raw11Q0Linear151'}],
 ['1RB1LC1RC1RB0LA1LD1LA0RE1RD1RF---1RD', {root:150,mod:'Raw11Q0Sweep150',ns:'BB6Coverage.Agent31Pump.Raw11Q0Sweep150'}],
 ['1RB1LC1RC1RD0LA1LA---0RE0RF1RE1RA0LC', {root:138,mod:'Raw11Q0Counter138',ns:'BB6Coverage.Agent31Pump.Multi.Raw11Q0Counter138'}],
 ['1RB1LC1RC0RD0LA1RB0RE1RE1LF0LA0LC---', {root:143,mod:'Raw11Q0Pair143Rules',ns:'BB6Coverage.Agent31Pump.Tails.Raw11Q0Pair143.M0'}],
 ['1RB1LC1RC0RD0LA1RB1RE0RF1LE0LC---0LB', {root:143,mod:'Raw11Q0Pair143Rules',ns:'BB6Coverage.Agent31Pump.Tails.Raw11Q0Pair143.M1'}],
]);
for (const x of require('./q0-143-ten-fixtures.json')) {
 const k=norm(x.table);
 if(regionCuts.has(k))throw Error('duplicate region cut '+k);
 regionCuts.set(k,{root:143,mod:'Raw11Q0Ten143',ns:'BB6Coverage.Agent31Pump.Tails.Raw11Q0Ten143.M'+x.index});
}
// Discovery-only extension for unresolved final-hole tables. The generated
// packed trace is still independently checked against the exact source table.
function findLongHole(a,limit=100000){
 if(a.filter(t=>t==='---').length!==1)return null;
 const tape=new Uint8Array(2*limit+5);let h=limit+2,q=0;
 for(let n=0;n<=limit;n++){
  const slot=2*q+tape[h],tr=a[slot];
  if(tr==='---')return {table:a.join(''),n,slot};
  tape[h]=+tr[0];h+=tr[1]==='R'?1:-1;q=tr.charCodeAt(2)-65;
 }
 return null;
}
const regionLeaves=[];
const repairs=new Map(),residuals=[],resIndex=new Map(),longs=[],census=new WeakMap(),external=new WeakMap();
const pre='Agent5Q0Coarse'+id,base=pre+'Base',longMod=pre+'Long',modules=[];
const stats={nodes:0,side:0,bank:0,far:0,split:0,last:0,pump:0,long:0,region:0,open:0,capped:0};
let B=summary.stats.bound;
function register(t,a,f){
 stats.nodes++;let n=1,x=false;
 if(t[0]==='h'&&t[3].length){
  stats.split++;
  if(a[t[2]]!=='---'||t[3].length!==4*Math.min(f+1,6))throw Error('bad branch '+a.join(''));
  for(let j=0;j<t[3].length;j++){const k=t[3][j];n+=register(k,fill(a,t[2],j),Math.max(f,1+(j>>2)));x=x||external.get(k)}
 }else if(t[0]==='h')stats.last++;
 else if(t[0]==='s')stats.side++;
 else if(t[0]==='a')stats.bank++;
 else if(t[0]==='f'){stats.far++;if(t[1].table!==a.join(''))throw Error('wrong FAR table')}
 else if(t[0]==='g'){stats.pump++;x=true;if(pumps.get(t[1])!==a.join(''))throw Error('wrong pump table')}
 else if(t[0]==='u'||t[0]==='c'){
  if(norm(t[1])!==a.join(''))throw Error('wrong residual table');
  const g=regionCuts.get(a.join(''));
  const c=longMap.get(a.join(''))||(!g&&t[0]==='u'?findLongHole(a):null);
  if(t[0]==='u'&&g){
   if(g.root!==id||a.filter(t=>t==='---').length!==1)throw Error('wrong region proof domain');
   t.splice(0,t.length,'v',regionLeaves.length);regionLeaves.push({...g,table:a.join('')});stats.region++;B=Math.max(B,g.minBound||0);x=true;
  }else if(t[0]==='u'&&c){
   if(a.filter(t=>t==='---').length!==1||a[c.slot]!=='---')throw Error('bad last repair');
   t.splice(0,t.length,'l',longs.length);longs.push({...c,table:a.join('')});B=Math.max(B,c.n+6);stats.long++;x=true;
  }else{
   stats[t[0]==='u'?'open':'capped']++;const key=a.join('');
   if(!resIndex.has(key)){resIndex.set(key,residuals.length);residuals.push(a.slice())}
   t.splice(0,t.length,'r',resIndex.get(key));x=true;
  }
 }else throw Error('bad node '+t[0]);
 census.set(t,n);external.set(t,x);return n;
}
const a=parse(summary.table),f=fresh(a);
if(register(tree,a,f)!==summary.stats.nodes)throw Error('wrong tree census');
const B0=B;
const imports=xs=>[...new Set(['FastPhaseTree','CachedPhaseTree','PhaseFrontier',...xs])].map(x=>'import '+x).join('\n')+'\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n';
const ns=n=>`namespace BB6.${n}\nopen BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree\n`;
function write(name,s){fs.writeFileSync(path.join(output,name+'.lean'),s);modules.push(name)}
const baseLines=[ns(base),`def parent : PartialMachine := ${table(a)}`];
for(let i=0;i<residuals.length;i++)baseLines.push(`def remaining${i} : PartialMachine := ${table(residuals[i])}`);
baseLines.push(`def remaining : List PartialMachine := [${residuals.map((_,i)=>'remaining'+i).join(',')}]\n`);
for(let i=0;i<residuals.length;i++)baseLines.push(`theorem mem${i} : remaining${i} ∈ remaining := by simp [remaining]`);
baseLines.push(`def ResidualHyp : Prop := ∀ p ∈ remaining, ∀ m, compatible p m → WeightedBound ${B} m\nend BB6.${base}\n`);
write(base,imports([])+baseLines.join('\n'));
const H=residuals.length?` (hR : BB6.${base}.ResidualHyp)`:'',arg=residuals.length?' hR':'';
const safeTy=p=>`∀ m, compatible ${p} m → WeightedBound ${B} m`;
const eq=(p,q)=>`have hEq : ${p} = ${q} := BB6.Agent47PhaseFrontier.sameTable_sound (by decide +kernel)\n  rw [hEq] at hm\n`;
// Packed long last-hole traces. The original-source lemma converts the packed
// final read slot to a knownRun first-hole witness without recomputing the run.
if(longs.length){
 for(let k=0;k<longs.length;k++){
  const name=longMod+k;
  const lines=[ns(name),'open BB6Coverage.Agent13PackedZipper BB6.Agent5FastPhaseTree'];
  const c=longs[k],t=parse(c.table),p='p'+k;
  lines.push(`def ${p} : PartialMachine := ${table(t)}`);
  lines.push(`def z${k}_0 : P := startP`);
  let q=0,l=0n,r=0n,prev=0;
  for(let i=1;i<=c.n;i++){
   const m=t[2*q+Number(l&1n)];if(m==='---')throw Error('premature hole '+c.table+' '+(i-1));
   const w=BigInt(m[0]);q=m.charCodeAt(2)-65;
   if(m[1]==='R'){l=(r&1n)+2n*(w+2n*(l>>1n));r>>=1n}else{l>>=1n;r=w+2n*r}
   if(i%256===0||i===c.n){
    const z=`z${k}_${i}`,zprev=`z${k}_${prev}`,s=`step${k}_${i}`,run=`run${k}_${i}`;
    lines.push(`def ${z} : P := ⟨${q},${l},${r}⟩`);
    lines.push(`theorem ${s} : runP ${p} ${i-prev} ${zprev} = some ${z} := by decide +kernel`);
    lines.push(`theorem ${run} : runP ${p} ${i} startP = some ${z} := ${prev===0?s:'joinP run'+k+'_'+prev+' '+s}`);
    prev=i;
   }
  }
  if(2*q+Number(l&1n)!==c.slot||t[c.slot]!=='---')throw Error('wrong final hole '+c.table);
  lines.push(`theorem safe${k} : ${safeTy(p)} := lastPacked ${B} ${p} ${c.n} ${slot(c.slot)} z${k}_${c.n} run${k}_${c.n} (by decide) (by decide) (by decide) (by decide) (by decide)\n#print axioms safe${k}`);
  lines.push(`end BB6.${name}\n`);write(name,imports([])+lines.join('\n'));
 }
}
function emit(t,a,f){
 switch(t[0]){
  case 's':return `(.side ${t[1]} ${t[2]} ${bit(t[3])} (${t[4]}))`;
  case 'a':{const c=sourceMitmCert(a.map(x=>x==='---'?24:moves.indexOf(x)),bank[t[1]],bank[t[2]]);if(!c)throw Error('bank mismatch '+a.join(''));return `(.automata ${cert(c)})`}
  case 'f':return `(.automata ${cert(t[1])})`;
  case 'h':return t[3].length?`(split ${t[1]} ${slot(t[2])} ${f} #[\n${t[3].map((k,j)=>emit(k,fill(a,t[2],j),Math.max(f,1+(j>>2)))).join(',\n')}])`:`(.last ${t[1]} ${slot(t[2])})`;
  default:throw Error('external tree emitted '+t[0]);
 }
}
function branch(t,f,p,name,children){
 return `theorem ${name}${H} : ${safeTy(p)} := by
  apply BB6.Agent5FastPhaseTree.splitFast ${B} ${p} ${t[1]} ${slot(t[2])} ${f} (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  have hcut : q.val ≤ ${f} := by simpa using h
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | ${children.map(n=>'exact '+n+arg).join(' | ')} | omega
`;
}
function local(t,a,f,p,name,lines,imps,allowSplit=false){
 const safe='safe'+name;
 if(allowSplit&&census.get(t)>MOD){
  const mn=pre+'Sub'+name,si=new Set([base]),sl=[ns(mn),`def parent : PartialMachine := ${table(a)}`];
  const s=local(t,a,f,'parent',name+'_r',sl,si,false);
  sl.push(`theorem safe${H} : ${safeTy('parent')} := ${s}${arg}\n#print axioms safe\nend BB6.${mn}\n`);
  write(mn,imports([...si])+sl.join('\n'));imps.add(mn);
  lines.push(`theorem ${safe}${H} : ${safeTy(p)} := by
  intro m hm
  ${eq(p,'BB6.'+mn+'.parent')}  exact BB6.${mn}.safe${arg} m hm\n`);return safe;
 }
 if(t[0]==='g'||t[0]==='l'||t[0]==='r'||t[0]==='v'){
  let other,proof;
  if(t[0]==='g'){imps.add('Raw11Q0CoarsePumps');other=pumpNS+'.p'+t[1];proof=`Cover.sound (${pumpNS}.cover${t[1]} ${B}) m hm`}
  else if(t[0]==='v'){const g=regionLeaves[t[1]];if(!g||g.table!==a.join(''))throw Error('wrong external region leaf');imps.add(g.mod);other=g.ns+'.'+(g.tableField||'table');proof=`Cover.sound (${g.ns}.cover ${B}${g.minBound?' (by decide)':''}) m hm`}
  else if(t[0]==='l'){const name=longMod+t[1];imps.add(name);other='BB6.'+name+'.p'+t[1];proof=`BB6.${name}.safe${t[1]} m hm`}
  else{other='BB6.'+base+'.remaining'+t[1];proof=`hR ${other} BB6.${base}.mem${t[1]} m hm`}
  lines.push(`theorem ${safe}${H} : ${safeTy(p)} := by
  intro m hm
  ${eq(p,other)}  exact ${proof}\n`);return safe;
 }
 if(census.get(t)<=CHUNK&&!external.get(t)){
  const c='cert'+name,h='checked'+name;
  lines.push(`def ${c} : Tree := ${emit(t,a,f)}\ntheorem ${h} : BB6.Agent5CachedPhaseTree.rootCheck ${B} ${p} ${c} = true := by decide +kernel\ntheorem ${safe}${H} : ${safeTy(p)} := BB6.Agent5CachedPhaseTree.sound ${B} _ ${c} (by decide) ${h}\n`);return safe;
 }
 if(t[0]!=='h'||!t[3].length)throw Error('expected split');
 const kids=[];
 for(let j=0;j<t[3].length;j++){
  const nm=name+'_'+j,cp='p'+nm;
  lines.push(`def ${cp} := refine ${p} ${slot(t[2])} (some ${move(j)})`);
  kids.push(local(t[3][j],fill(a,t[2],j),Math.max(f,1+(j>>2)),cp,nm,lines,imps,true));
 }
 lines.push(branch(t,f,p,safe,kids));return safe;
}
const imps=new Set([base]),lines=[ns(pre),`def parent : PartialMachine := BB6.${base}.parent`];
const rootSafe=local(tree,a,f,'parent','_root',lines,imps,false);
if(residuals.length)lines.push(`theorem cover_from_remaining (hR : BB6.${base}.ResidualHyp) : Cover (WeightedBound ${B}) parent := .leaf _ (${rootSafe} hR)\n#print axioms cover_from_remaining`);
else lines.push(`theorem cover : Cover (WeightedBound ${B}) parent := .leaf _ ${rootSafe}\n#print axioms cover`);
lines.push(`end BB6.${pre}\n`);write(pre,imports([...imps])+lines.join('\n'));
const manifest={id,table:summary.table,bound:B,stats,remaining:residuals.map(a=>a.join('').match(/.{6}/g).join('_')),regionLeaves,longs,modules,chunk:CHUNK,moduleLimit:MOD,theorem:'BB6.'+pre+'.'+(residuals.length?'cover_from_remaining':'cover')};
fs.writeFileSync(path.join(output,'manifest.json'),JSON.stringify(manifest,null,2)+'\n');console.log(JSON.stringify({...manifest,modules:modules.length}));
