'use strict';
// First-pass retained-tree scan of the 18 five-hole Raw11-extra parents.
// This is a computational triage artifact, not a proof or a parent Cover.
const fs = require('node:fs');
const path = require('node:path');
const { search } = require('./generate-raw11-extra.cjs');
const route = require('./raw11-route.json');
const cap = Number(process.argv[2] || 12000);
const normalize = s => s.replaceAll('_', '');
const candidates = route.extra.map((table, id) => ({
  id, table, holes: (table.match(/---/g) || []).length
})).filter(x => x.holes === 5);
const results = [];
for (const p of candidates) {
  try {
    const r = search(p.table, { retain: true, cap });
    results.push({
      id: p.id, table: p.table, holes: p.holes, cap,
      completeTree: !!r.tree, nodes: r.n, bound: r.bound,
      stats: r.stats, openLeaves: r.opens.map(normalize)
    });
  } catch (e) {
    results.push({
      id: p.id, table: p.table, holes: p.holes, cap,
      completeTree: false, error: String(e)
    });
  }
}
const leafParents = {};
for (const r of results) for (const leaf of r.openLeaves || []) {
  (leafParents[leaf] ||= []).push(r.id);
}
const duplicates = Object.entries(leafParents)
  .filter(([, ids]) => ids.length > 1)
  .map(([table, ids]) => ({ table, parentIds: ids }));
const report = {
  kind: 'computational-triage-only',
  cap,
  candidateCount: candidates.length,
  completedTrees: results.filter(r => r.completeTree).length,
  cappedOrFailed: results.filter(r => !r.completeTree).map(r => r.id),
  totalNodes: results.reduce((n, r) => n + (r.nodes || 0), 0),
  openLeafCount: results.reduce((n, r) => n + (r.openLeaves || []).length, 0),
  duplicateOpenLeavesAcrossParents: duplicates,
  parents: results
};
fs.writeFileSync(path.join(__dirname, 'raw11-extra-5hole-scan.json'),
  JSON.stringify(report, null, 2) + '\n');
console.log(JSON.stringify({
  cap, candidateCount: report.candidateCount,
  completedTrees: report.completedTrees,
  cappedOrFailed: report.cappedOrFailed,
  totalNodes: report.totalNodes,
  openLeafCount: report.openLeafCount,
  duplicateLeafTables: duplicates.length
}));
