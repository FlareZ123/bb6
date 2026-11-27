#!/usr/bin/env node
const fs=require("fs"), path=require("path");
const root=__dirname;
const api=new Function(fs.readFileSync(path.join(root,"discover_abstract.js"),"utf8"))();
const v=(process.argv[2]||"").toLowerCase();
if(!new Set(["1la","1lb","1lf","1rf"]).has(v)) throw new Error("variant 1la/1lb/1lf/1rf");
const srcPath=process.argv[3] || path.join(root,`spec_b0le_e${v}.json`);
const outPath=process.argv[4] || `/tmp/spec_b0le_e${v}_abstract.json`;
const j=JSON.parse(fs.readFileSync(srcPath,"utf8"));
j.bidfa ||= {};
const remain=[]; let hits=0;
for(const row of j.unresolved||[]){
  const z=api.search(row.table,20000);
  if(z.status==="ok"){
    j.bidfa[String(row.i)]={table:row.table,status:"ok",dfa:z.dfa,states:z.states,edges:z.edges,params:z.params};
    hits++;
  } else remain.push(row);
}
j.unresolved=remain;
fs.writeFileSync(outPath,JSON.stringify(j,null,2)+"\n");
console.log(JSON.stringify({variant:v,hits,remaining:remain.length,output:outPath}));
