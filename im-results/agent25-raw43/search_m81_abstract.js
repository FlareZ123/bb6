#!/usr/bin/env node
const fs=require("fs"),path=require("path");
const api=new Function(fs.readFileSync(path.join(__dirname,"discover_abstract.js"),"utf8"))();
const table="1RB1LF_1RC0LE_0RD0RB_1LD0RB_1RF---_0LA0LB";
const fam=(process.argv[2]||"run").toLowerCase();
const cap=120000;
let tests=[];
function add(kind,l,r){tests.push([kind,l,r])}
const rightChunks=[];
for(const width of [2,3,4])for(let k=1;k<=4;k++)for(const c of [1,2,3])for(const m of [1,2,3])
  rightChunks.push({width,k,c,m});
if(fam==="run"){
 const left=[];
 for(let k=1;k<=6;k++)for(const c of [1,2,3,4])for(const m of [1,2,3,4])left.push([k,c,c,m,m]);
 for(const l of left)for(const r of rightChunks.filter(x=>x.width===2&&x.k<=2))add("run/chunk",l,r);
}else if(fam==="lag"){
 const left=[];
 for(let lag=1;lag<=6;lag++)for(const c of [1,2,3,4])for(const m of [1,2,3,4])
   left.push({lag:[lag,c,c,m,m]});
 for(const l of left)for(const r of rightChunks.filter(x=>x.width<=3&&x.k<=2))add("lag/chunk",l,r);
}else if(fam==="chunk"){
 const left=[];
 for(const width of [2,3,4])for(let k=1;k<=5;k++)for(const c of [1,2,3,4])for(const m of [1,2,3,4])
   left.push({width,k,c,m});
 for(const l of left)for(const r of rightChunks.filter(x=>x.width===2&&x.k<=3))add("chunk/chunk",l,r);
}else if(fam==="block"){
 const left=[];
 for(const k of [8,12,16,20,24,32])for(const periods of [[2],[3],[4],[2,3],[2,4],[3,4]])
   for(const c of [1,2,3,4])for(const m of [1,2,3,4])left.push({k,periods,c,m});
 for(const l of left)for(const r of rightChunks.filter(x=>x.width===2&&x.k<=2))add("block/chunk",l,r);
}else throw new Error("family run|lag|chunk|block");
let best={states:0},tested=0;
for(const [kind,l,r] of tests){
 const z=api.solve(table,l,r,cap);tested++;
 if(z.states>best.states)best={kind,l,r,status:z.status,states:z.states};
 if(z.status==="ok"){
   console.log(JSON.stringify({status:"ok",fam,tested,kind,left:l,right:r,states:z.states,edges:z.edges,dfa:z.dfa}));
   process.exit(0);
 }
 if(tested%250===0)console.log(JSON.stringify({status:"progress",fam,tested,best}));
}
console.log(JSON.stringify({status:"none",fam,tested,best}));
process.exit(2);
