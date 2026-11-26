'use strict';
// Expand only the five capped five-hole Raw11 extra parents. Run from repo root:
// node im-results/agent5-weighted-tnf-queue/scan-raw11-capped-five.cjs
const fs = require('node:fs');
const path = require('node:path');
const { search } = require('../agent47-raw11-adapter/generate-raw11-extra.cjs');
const route = require('../agent47-raw11-adapter/raw11-route.json');
const ids = [127,128,129,130,140];
const result = [];
for (const id of ids) {
  const r = search(route.extra[id], { retain:true, cap:100000 });
  if (!r.tree) throw Error('incomplete parent '+id);
  const row = {id,table:r.table,nodes:r.n,bound:r.bound,stats:r.stats,opens:r.opens};
  if (Object.values(row.stats).reduce((a,b)=>a+b,0)+row.opens.length!==row.nodes) throw Error('bad counts');
  result.push(row);
  console.log(JSON.stringify(row));
}
fs.writeFileSync(path.join(__dirname,'raw11-capped-five.json'),JSON.stringify(result,null,2)+'\n');
