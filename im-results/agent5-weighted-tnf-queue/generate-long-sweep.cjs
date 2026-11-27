'use strict';
// Untrusted finite-trace compressor. Every macro is checked by PackedSweep in Lean.
// Local block matches use exact head-inclusive left and head-exclusive right words.
function accelerate(table,limit,K=18){
 const a=table.replaceAll("_","").match(/.../g);
 if(a.length!==12||a.filter(t=>t==="---").length!==1)throw Error("expected a single-hole table");
 const read=z=>a[2*z.q+ +(z.L[0]||0)];
 function step(z){
  const v=read(z);if(v==="---")return null;
  return v[1]==="R"?{q:v.charCodeAt(2)-65,L:(z.R[0]||"0")+v[0]+z.L.slice(1),R:z.R.slice(1),h:z.h+1}:
    {q:v.charCodeAt(2)-65,L:z.L.slice(1),R:v[0]+z.R,h:z.h-1};
 }
 function find(z){
  let u=z,lo=0,hi=0,best=null;
  for(let k=1;k<=K;k++){
   u=step(u);if(!u)break;
   const d=u.h-z.h;lo=Math.min(lo,d);hi=Math.max(hi,d);
   if(u.q!==z.q||!d)continue;
   const b=Math.abs(d),lp=d>0?1-lo:1-lo-b,rp=d>0?hi-b:hi;
   if(lp<0||rp<0||z.L.length<lp+(d<0?b:0)||z.R.length<rp+(d>0?b:0))continue;
   if(z.L.slice(0,lp)!==u.L.slice(0,lp)||z.R.slice(0,rp)!==u.R.slice(0,rp))continue;
   const src=d>0?z.R:z.L,dst=d>0?u.L:u.R,sp=d>0?rp:lp,dp=d>0?lp:rp;
   const I=src.slice(sp,sp+b),O=dst.slice(dp,dp+b);
   let n=1;while(src.slice(sp+n*b,sp+(n+1)*b)===I)n++;
   if(n<2||k*n<16||best&&k*n<=best.k*best.n)continue;
   const L=d>0?z.L.slice(0,lp)+O.repeat(n)+z.L.slice(lp):z.L.slice(0,lp)+z.L.slice(lp+n*b);
   const R=d>0?z.R.slice(0,rp)+z.R.slice(rp+n*b):z.R.slice(0,rp)+O.repeat(n)+z.R.slice(rp);
   best={k,n,d,lp:z.L.slice(0,lp),rp:z.R.slice(0,rp),I,O,end:{q:z.q,L,R,h:z.h+d*n}};
  }
  return best;
 }
 const start={q:0,L:"",R:"",h:0};let z=start,n=0,macro=0,plain=0,pending=0;
 const groups=[];let groupStart=z,groupTime=0,ops=[];
 function flushPlain(){if(pending){ops.push({steps:pending});pending=0}}
 function flush(){flushPlain();if(ops.length){groups.push({start:groupStart,end:z,n:n-groupTime,ops});ops=[];groupStart=z;groupTime=n}}
 while(n<limit&&read(z)!=="---"){
  const m=find(z);
  if(m&&n+m.k*m.n<=limit){flushPlain();const {end,...op}=m;ops.push(op);z=end;n+=m.k*m.n;macro++}
  else {z=step(z);n++;pending++;plain++;if(pending===128)flushPlain()}
  if(ops.length>=64)flush();
 }
 flush();
 return {n,macro,plain,groups,slot:2*z.q+ +(z.L[0]||0),halt:read(z)==="---"};
}
const fixtures=[
 {root:150,table:"1RB1LC_1RC1RF_0LA1LD_0LE0RB_1LA---_1RA0LA",n:1102620,slot:9},
 {root:150,table:"1RB1LC_1RC1RF_0LA1LD_0LB0RE_0LC1RD_1RA---",n:13007746,slot:11},
 {root:149,table:"1RB1LC_1RC---_0LA0RD_1RF1RE_0RD0RB_1LA0LC",n:195830,slot:3}
];
function emit(f,dir,mod){
 const fs=require("node:fs"),path=require("node:path");
 const {table,slot}=require("../agent47-raw11-adapter/generate-q0-lean.cjs");
 const r=accelerate(f.table,f.n);
 if(!r.halt||r.n!==f.n||r.slot!==f.slot)throw Error("wrong expected first hole: "+JSON.stringify({f,n:r.n,slot:r.slot}));
 fs.mkdirSync(dir,{recursive:true});
 const bits=s=>"["+[...s].map(b=>b==="1"?"true":"false").join(",")+"]";
 const pack=s=>s.length?BigInt("0b"+[...s].reverse().join("")):0n;
 const point=z=>"⟨"+z.q+","+pack(z.L)+","+pack(z.R)+"⟩";
 const op=o=>o.steps?".steps "+o.steps:(o.d>0?".right ":".left ")+[o.lp,o.rp,o.I,o.O].map(bits).join(" ")+" "+o.k+" "+o.n;
 const common=["import Agent5PackedSweep","set_option maxRecDepth 100000","set_option maxHeartbeats 0","open BB6Coverage BB6Coverage.Agent13PackedZipper BB6.Agent5PackedSweep BB6.Agent5FastPhaseTree BB6.Agent13BlankDelay"];
 const base=mod+"Base",parts=[],modules=[base];
 fs.writeFileSync(path.join(dir,base+".lean"),common.join("\n")+"\nnamespace BB6."+mod+"\ndef table : PartialMachine := "+table(f.table.replaceAll("_","").match(/.../g))+"\nend BB6."+mod+"\n");
 // Independent contiguous segments; no repeated compilation of earlier steps.
 for(let i=0;i<r.groups.length;i+=8){
  const name=mod+"Part"+parts.length,ns="BB6."+name;
  const lines=["import "+base,...common,"namespace "+ns,"open BB6."+mod];
  let j=0,time=0;
  for(const g of r.groups.slice(i,i+8)){
   if(j===0)lines.push("def z0 : P := "+point(g.start));
   lines.push("def z"+(j+1)+" : P := "+point(g.end),"def ops"+j+" : List Action := ["+g.ops.map(op).join(",\n")+"]",
    "theorem step"+j+" : runP table "+g.n+" z"+j+" = some z"+(j+1)+" := traceRun_sound table ops"+j+" z"+j+" (out := ("+g.n+",z"+(j+1)+")) (by decide +kernel)",
    "theorem run"+j+" : runP table "+(time+g.n)+" z0 = some z"+(j+1)+" := "+(j?"joinP_at table "+time+" "+g.n+" "+(time+g.n)+" z0 z"+j+" z"+(j+1)+" rfl run"+(j-1)+" step"+j:"step"+j));
   time+=g.n;j++;
  }
  lines.push("theorem segment : runP table "+time+" z0 = some z"+j+" := run"+(j-1),"#print axioms segment","end "+ns);
  fs.writeFileSync(path.join(dir,name+".lean"),lines.join("\n")+"\n");modules.push(name);parts.push({name,time,end:"BB6."+name+".z"+j});
 }
 const lines=[...parts.map(x=>"import "+x.name),...common,"namespace BB6."+mod];
 let time=0;for(let i=0;i<parts.length;i++){let p=parts[i],prev=time;time+=p.time;lines.push("theorem prefix"+i+" : runP table "+time+" startP = some "+p.end+" := "+(i?"joinP_at table "+prev+" "+p.time+" "+time+" startP "+parts[i-1].end+" "+p.end+" rfl prefix"+(i-1)+" BB6."+p.name+".segment":"BB6."+p.name+".segment"))}
 const end=parts.at(-1).end;
 lines.push("theorem cover (B : Nat) (h : "+(r.n+6)+" ≤ B) : Cover (WeightedBound B) table := Cover.leaf table (lastPacked B table "+r.n+" "+slot(r.slot)+" "+end+" prefix"+(parts.length-1)+" (by decide) (by decide) (by decide) (by decide) h)","#print axioms cover","end BB6."+mod);
 fs.writeFileSync(path.join(dir,mod+".lean"),lines.join("\n")+"\n");modules.push(mod);
 return {root:f.root,table:f.table,n:f.n,slot:f.slot,macro:r.macro,plain:r.plain,groups:r.groups.length,modules,mod};
}
module.exports={accelerate,fixtures,emit};
if(require.main===module){
 const idx=Number(process.argv[2]),out=process.argv[3],f=fixtures[idx],mod="Raw11Q0LongSweep"+idx;
 if(!f||!out)throw Error("usage: fixture-index output-dir");
 const r=emit(f,out,mod);require("node:fs").writeFileSync(require("node:path").join(out,"manifest.json"),JSON.stringify(r,null,2)+"\n");console.log(JSON.stringify(r));
}
