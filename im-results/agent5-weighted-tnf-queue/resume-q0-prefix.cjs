'use strict';
// Resume only capped nodes of a frozen discovery tree. Existing certificates
// and unresolved non-cap leaves remain byte-for-byte unchanged.
const {moves,fmt}=require('./scan-q0-coarse-full.cjs');
const {scanPrefix}=require('./scan-q0-prefix.cjs');
function resume(table,tree,options={}){
 const {cap=2000000,ms=Infinity}=options,start=Date.now();
 let processed=0,replaced=0,retained=0;
 const stats={nodes:0,side:0,auto:0,far:0,split:0,last:0,pump:0,open:0,cap:0,bound:0};
 const opens=[],pending=[];
 const parse=t=>t.replaceAll('_','').match(/.{3}/g).map(x=>x==='---'?24:moves.indexOf(x));
 const initial=parse(table);
 const fresh=Math.max(...initial.map((x,i)=>x===24?0:Math.max(1+(i>>1),1+(x>>2))));
 function visit(a,f,t,allow){
  if(!Array.isArray(t))throw Error('invalid node');
  if(t[0]==='c'&&allow&&processed<cap&&Date.now()-start<ms){
   if(t[1]!==fmt(a))throw Error('capped table mismatch');
   const z=scanPrefix(t[1],{...options,cap:cap-processed,ms:ms-(Date.now()-start)});
   processed+=z.processed;replaced++;
   return visit(a,f,z.tree,false);
  }
  if(allow)retained++;
  stats.nodes++;
  switch(t[0]){
  case 'c':case 'u':
   if(t[1]!==fmt(a))throw Error('residual table mismatch');
   if(t[0]==='c'){stats.cap++;pending.push(t[1]);}else{stats.open++;opens.push(t[1]);}
   return t;
  case 's':stats.side++;return t;
  case 'a':stats.auto++;return t;
  case 'f':if(t[1].table!==fmt(a).replaceAll('_',''))throw Error('FAR mismatch');stats.far++;return t;
  case 'g':stats.pump++;return t;
  case 'h':{
   const [_,n,i,kids]=t;
   if(a[i]!==24||!Number.isSafeInteger(n)||n<0)throw Error('invalid hole');
   stats.bound=Math.max(stats.bound,n+6);
   if(a.filter(x=>x===24).length===1){if(kids.length)throw Error('last branches');stats.last++;return t;}
   stats.split++;
   if(kids.length!==4*Math.min(f+1,6))throw Error('normalized branching mismatch');
   return ['h',n,i,kids.map((child,k)=>{let b=a.slice();b[i]=k;return visit(b,Math.max(f,1+(k>>2)),child,allow)})];
  }
  default:throw Error('unknown node '+t[0]);
  }
 }
 if(initial.length!==12||initial.some(x=>x<0))throw Error('invalid table');
 const result=visit(initial,fresh,tree,true);
 if(stats.nodes!==stats.side+stats.auto+stats.far+stats.split+stats.last+stats.pump+stats.open+stats.cap)throw Error('census mismatch');
 return {table,stats,opens,pending,tree:result,complete:!opens.length&&!pending.length,processed,replaced,retained,elapsedMs:Date.now()-start};
}
module.exports={resume};
if(require.main===module){
 const fs=require('node:fs'),path=require('node:path');
 const {search,searchPeriodic}=require('./q0-open-automata.cjs');
 const {verify}=require('./verify-coarse-pumps.cjs');
 const pumps=require('./q0-coarse-pumps.json');for(const c of pumps)verify(c);
 const known=new Map(pumps.map(c=>[c.table,c.root]));
 const route=require('../agent47-raw11-adapter/raw11-route.json');
 const id=+process.argv[2],input=process.argv[3],out=process.argv[4],cap=+(process.argv[5]||2000000);
 const old=JSON.parse(fs.readFileSync(path.join(input,'summary.json')));
 if(!Number.isSafeInteger(id)||!route.targets[id]||old.id!==id||old.table!==route.targets[id]||!out||!Number.isSafeInteger(cap)||cap<1)throw Error('usage: resume id old-dir out-dir [cap]');
 const tree=JSON.parse(fs.readFileSync(path.join(input,'tree.json')));
 const {tree:result,...summary}=resume(old.table,tree,{search,searchPeriodic,known,cap});
 summary.id=id;summary.cap=cap;summary.scanner='shared-prefix-resume-v1';summary.previousStats=old.stats;
 fs.mkdirSync(out,{recursive:true});
 fs.writeFileSync(path.join(out,'summary.json'),JSON.stringify(summary,null,2)+'\n');
 fs.writeFileSync(path.join(out,'tree.json'),JSON.stringify(result));
 console.log(JSON.stringify(summary));
}
