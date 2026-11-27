// Untrusted automatic discovery for exact or partial residual tables.
// The only accepted result is the independently kernel-checked Lean witness.
const fs=require("fs"),path=require("path");
const {discover,discoverBlock,compress}=require("./run_summary_search.js");
const {emit}=require("./emit_run_summary.js");
const [input,output,family]=process.argv.slice(2);
if(!/^[A-Za-z][A-Za-z0-9]*$/.test(family))throw Error("invalid Lean module stem");
const machines=JSON.parse(fs.readFileSync(input,"utf8"));
const symmetric=[[2,3,1,0],[3,3,1,0],[3,3,3,3],[4,3,1,0],[3,4,1,0],[4,4,1,0],[3,3,1,1],[3,3,1,2],[3,3,1,3],[4,3,1,2],[5,5,3,1,1,0],[4,5,3,1,1,0],[5,4,3,1,1,0],[4,4,2,1,1,0],[4,3,4,1,1,0],[5,4,4,1,1,0]];
const asymmetric=[
 [[2,3,1,0],[4,5,3,1,1,0]],[[3,3,1,0],[5,5,3,1,1,0]],
 [[5,5,3,1,1,0],[2,3,1,0]],[[3,3,3,3],[3,3,1,0]],
 [[3,3,1,0],[3,3,3,3]],[[4,3,1,2],[3,3,1,0]],
 [[3,3,1,0],[4,3,1,2]],[[3,3,3,3],[3,3,3,3]]
];
const params=[...symmetric.map(x=>[x,x]),...asymmetric];
const blocks=[];for(let w=2;w<=7;w++)for(let k of [1,2,3])for(let c of [1,2,3])blocks.push([w,k,c,1]);
fs.mkdirSync(output,{recursive:true});
const found=[],missing=[];
for(let i=0;i<machines.length;i++){
 const m=machines[i];let cert=null,used=null;
 for(const [l,r] of params){let raw=discover(m,l,r,25000);if(raw){cert=compress(m,raw.L,raw.R);used=[l,r];break}}
 if(!cert){for(const p of blocks){let raw=discoverBlock(m,p,p,25000);if(raw){cert=compress(m,raw.L,raw.R);used={block:[p,p]};break}}}
 if(!cert){missing.push(m);continue}
 const mod=family+"AutoRun"+i, entry={machine:m,L:cert.L,R:cert.R,count:cert.count,params:used,history:cert.history};
 fs.writeFileSync(path.join(output,mod+".lean"),emit({0:entry},mod));
 fs.writeFileSync(path.join(output,mod+".json"),JSON.stringify(entry)+"\n");
 found.push({table:m,module:mod,namespace:"BB6.Agent13."+mod+".M0",count:cert.count});
}
const result={found,missing};fs.writeFileSync(path.join(output,"auto-run-manifest.json"),JSON.stringify(result,null,2)+"\n");
console.log("run-summary fallback: "+found.length+" closed / "+missing.length+" unresolved (candidate, kernel check required)");
