#!/usr/bin/env node
// Second-line abstraction search for the small B0LE residual frontier.
// Discovery only: every successful automaton is independently checked in Lean later.
const fs=require("fs"),path=require("path");
const api=new Function(fs.readFileSync(path.join(__dirname,"discover_abstract.js"),"utf8"))();
const input=process.argv[2], output=process.argv[3];
const j=JSON.parse(fs.readFileSync(input,"utf8")); j.bidfa ||= {};
const remain=[]; let hits=0; const byKind={window:0,lag:0,chunk:0,run:0};
function trySolve(t){
  for(let l=1;l<=12;l++) for(let r=1;r<=12;r++){
    const z=api.solve(t,l,r,50000);
    if(z.status==="ok") return ["window",z];
  }
  const cm=[[1,1],[1,2],[2,1],[2,2],[3,1],[1,3],[3,2],[2,3],[4,1],[1,4]];
  for(let k=1;k<=5;k++) for(const [c,m] of cm){
    const p={lag:[k,c,c,m,m]},z=api.solve(t,p,p,60000);
    if(z.status==="ok") return ["lag",z];
  }
  for(const width of [2,3,4]) for(let k=1;k<=3;k++)
    for(let c=1;c<=3;c++) for(let m=1;m<=3;m++){
      const p={width,k,c,m},z=api.solve(t,p,p,60000);
      if(z.status==="ok") return ["chunk",z];
    }
  const ds=[[3,1,1,1,1],[4,1,1,1,1],[5,1,1,1,1],[3,2,2,1,1],[4,2,2,1,1],
            [3,1,1,2,2],[4,1,1,2,2],[5,2,2,2,2]];
  for(const l of ds) for(const r of ds){
    const z=api.solve(t,l,r,60000);
    if(z.status==="ok") return ["run",z];
  }
  return null;
}
for(const row of j.unresolved||[]){
  const got=trySolve(row.table);
  if(got){
    const [kind,z]=got;
    j.bidfa[String(row.i)]={table:row.table,status:"ok",dfa:z.dfa,states:z.states,edges:z.edges,params:z.params,kind};
    hits++; byKind[kind]++;
  } else remain.push(row);
}
j.unresolved=remain;
fs.writeFileSync(output,JSON.stringify(j,null,2)+"\n");
console.log(JSON.stringify({hits,remaining:remain.length,byKind,remainingRows:remain.map(x=>({i:x.i,table:x.table})),output}));
