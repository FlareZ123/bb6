const fs=require("node:fs"), path=require("node:path");
const {find,emit}=require("./coarse-pair.cjs");
const base=__dirname;
const q0=JSON.parse(fs.readFileSync(path.join(base,"q0-export/pilot-0-100-fuel-1000000.json"),"utf8"));
const indices=[33,34,39,44,46,48,49,51];

function inspect(tree){
  const stats={nodes:0,side:0,mitm:0,last:0,split:0,open:0,bad:0};
  const openTables=new Map();
  let maxHalt=0;
  function walk(t){
    stats.nodes++;
    if(t[0]==="s"){stats.side++;return;}
    if(t[0]==="p"){stats.mitm++;return;}
    if(t[0]==="o"){
      stats.open++;
      openTables.set(t[1],(openTables.get(t[1])||0)+1);
      return;
    }
    if(t[0]==="h"){
      maxHalt=Math.max(maxHalt,t[1]);
      if(!t[3]||t[3].length===0){stats.last++;return;}
      stats.split++;
      for(const child of t[3])walk(child);
      return;
    }
    stats.bad++;
  }
  walk(tree);
  return {stats,maxHalt,bound:maxHalt+6,
    openTables:[...openTables.entries()].map(([table,count])=>({table,count})).sort((a,b)=>b.count-a.count)};
}

const results=[];
for(const i of indices){
  const row=q0.active[i];
  if(!row)throw new Error("missing q0 active root "+i);
  const started=Date.now();
  try{
    const found=find(row,true);
    if(!found||!found.tree){results.push({index:i,table:row.table,holes:row.holes,fresh:row.fresh,status:"no-tree",search_n:found?.n??null,elapsed_ms:Date.now()-started});continue;}
    const x=inspect(found.tree);
    results.push({index:i,table:row.table,holes:row.holes,fresh:row.fresh,status:"tree",search_n:found.n,elapsed_ms:Date.now()-started,coqTree:x.stats.open===0?emit(found.tree):null,...x});
  }catch(e){
    results.push({index:i,table:row.table,holes:row.holes,fresh:row.fresh,status:"error",error:String(e),elapsed_ms:Date.now()-started});
  }
}
const summary={source:"q0-export/pilot-0-100-fuel-1000000.json",indices,results,
  distinctOpenTables:[...new Set(results.flatMap(x=>x.openTables||[]).map(x=>x.table))].length};
const out=process.argv[2]||path.join(base,"q0-sibling-scan.json");
fs.writeFileSync(out,JSON.stringify(summary,null,2)+"\n");
console.log(JSON.stringify(results.map(x=>({index:x.index,status:x.status,search_n:x.search_n,elapsed_ms:x.elapsed_ms,stats:x.stats,distinctOpenTables:x.openTables?.length})),null,2));
