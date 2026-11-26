'use strict';
// Generate exact finite-tree Covers for the 11 five-hole Raw11-extra parents
// whose retained search trees have no unresolved leaves.
const fs = require('node:fs');
const path = require('node:path');
const { search, generateRoot } = require('./generate-raw11-extra.cjs');
const route = require('./raw11-route.json');

const expected = {
  85: { nodes: 8829, bound: 195 },
  86: { nodes: 8613, bound: 98 },
  87: { nodes: 7557, bound: 101 },
  88: { nodes: 7557, bound: 91 },
  89: { nodes: 10893, bound: 87 },
  90: { nodes: 6669, bound: 41 },
  125: { nodes: 6693, bound: 47 },
  135: { nodes: 8157, bound: 245 },
  136: { nodes: 7797, bound: 123 },
  138: { nodes: 8589, bound: 97 },
  139: { nodes: 8541, bound: 147 }
};

const results = [];
for (const [key, want] of Object.entries(expected)) {
  const id = Number(key);
  const table = route.extra[id];
  if (typeof table !== 'string') throw new Error('missing Raw11 extra parent ' + id);
  const r = search(table, { retain: true, cap: 12000 });
  if (!r.tree || r.opens.length !== 0)
    throw new Error('parent ' + id + ' is not a closed retained tree: ' +
      JSON.stringify({ nodes: r.n, opens: r.opens }));
  if (r.n !== want.nodes || r.bound !== want.bound)
    throw new Error('parent ' + id + ' search changed: ' +
      JSON.stringify({ expected: want, actual: { nodes: r.n, bound: r.bound, stats: r.stats } }));
  const source = [
    'import PhaseTree',
    'set_option maxHeartbeats 0',
    'set_option maxRecDepth 100000',
    generateRoot(id, r)
  ].join('\n') + '\n';
  fs.writeFileSync(path.join(__dirname, `Raw11Extra${id}.lean`), source);
  results.push({
    id, table, holes: 5, nodes: r.n, bound: r.bound,
    stats: r.stats, openLeaves: []
  });
}
fs.writeFileSync(path.join(__dirname, 'raw11-extra-5hole-closed-manifest.json'),
  JSON.stringify(results, null, 2) + '\n');
console.log(JSON.stringify(results.map(({id,nodes,bound,stats}) => ({id,nodes,bound,stats}))));
