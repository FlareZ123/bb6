// First-use canonical certificate discovery; the Lean CanonicalFastAudit
// checker independently enforces every omitted-label condition.
const fs=require('fs'),zlib=require('zlib');
const {makeSearch}=require('./search.cjs');
const spec=require('./candidate.json');
function bank(){
 const rows=zlib.gunzipSync(Buffer.from(fs.readFileSync(require.resolve('../agent7-raw36-transfer/fixture.tsv.gz.b64'),'utf8'),'base64')).toString().trim().split(/\n/).map(x=>x.trim().split(/\s+/));
 return [...spec.codes,'101230333','101023202',...rows.map(x=>x[1])];
}
function canonicalRun(parent,cut,emit=false,opts={}) {
 const options={...spec.options,maxNodes:5000000,...opts};
 const engine=makeSearch(bank(),options),p=engine.parse(parent);
 if(!(cut>0&&cut<=6&&p.every((mv,s)=>mv<0||(s>>1)<cut&&mv%6<cut)))throw Error('parent support');
 const stats={nodes:0,split:0,cycle:0,far:0,last:0,open:0,halt:0,score:0};
 const mass={halt:0n,nonhalt:0n,open:0n};const opens=[];const pow25=n=>25n**BigInt(n);
 function walk(c,mult){
  if(++stats.nodes>options.maxNodes)throw Error('node limit; no exhaustive result');
  const holes=p.filter(x=>x<0).length;let a=engine.short(p);
  if(a[0]==='open'){
   for(const df of engine.bank){const code=engine.far(p,df);if(code){stats.far++;mass.nonhalt+=mult*pow25(holes);return emit?['far',code]:null;}}
   a=engine.long(p);
  }
  if(a[0]==='cycle'){stats.cycle++;mass.nonhalt+=mult*pow25(holes);return emit?a:null;}
  if(a[0]==='open'){stats.open++;mass.open+=mult*pow25(holes);const table=engine.show(p);opens.push(table);return emit?['open',table]:null;}
  const [,n,s]=a;if(!(holes&&p[s]<0&&(s>>1)<c))throw Error('first hole outside introduced support');
  stats.halt++;stats.score=Math.max(stats.score,n+6);mass.halt+=mult*pow25(holes-1);
  if(holes===1){stats.last++;mass.nonhalt+=24n*mult;return emit?['last',n,s]:null;}
  stats.split++;const kids=[];
  for(let mv=0;mv<24;mv++){
   const q=mv%6;
   if(q>c){if(emit)kids.push(['skip']);continue;}
   p[s]=mv;const k=walk(Math.max(c,q+1),mult*BigInt(q===c?6-c:1));if(emit)kids.push(k);
  }
  p[s]=-1;return emit?['split',n,s,kids]:null;
 }
 const expected=pow25(p.filter(x=>x<0).length),tree=walk(cut,1n);
 if(mass.halt+mass.nonhalt+mass.open!==expected)throw Error('weighted partition mass');
 return {parent,cut,stats,mass:Object.fromEntries(Object.entries(mass).map(([k,v])=>[k,String(v)])),expected:String(expected),opens,...(emit?{tree}:{})};
}
module.exports={canonicalRun,bank};
if(require.main===module){const [parent,cut,emit]=process.argv.slice(2);process.stdout.write(JSON.stringify(canonicalRun(parent,Number(cut),emit==='tree'))+'\n');}
