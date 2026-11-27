const fs=require("fs"),path=require("path");
const {discover,discoverBlock,compress}=require("./run_summary_search.js");
const {emit}=require("./emit_run_summary.js");
const data=JSON.parse(fs.readFileSync(path.join(__dirname,"d17v24-pair-blocks.json"),"utf8"));
for(const [id,d] of Object.entries(data)){
 const raw=(d.kind==="block"?discoverBlock:discover)(d.machine,d.lp,d.rp,25000);
 if(!raw)throw Error("failed to rediscover "+id);
 const c=compress(d.machine,raw.L,raw.R);
 if(JSON.stringify([c.L,c.R,c.count])!==JSON.stringify([d.L,d.R,d.count]))throw Error("different quotient "+id);
}
process.stdout.write(emit(data,"Box33D17V24PairBlocks"));
