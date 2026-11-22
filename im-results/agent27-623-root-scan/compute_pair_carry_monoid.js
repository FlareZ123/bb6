#!/usr/bin/env node
// Recompute the full transformation monoid of the 66-state paired-carry closure.
// Run from any directory: node compute_pair_carry_monoid.js
const fs = require('node:fs');
const path = require('node:path');
const crypto = require('node:crypto');
const sourcePath = path.join(__dirname, '../agent49-parity623/PostResetCarryPairClosure.json');
const outputPath = path.join(__dirname, 'PairCarryTransformationMonoid.json');
const raw = fs.readFileSync(sourcePath);
const closure = JSON.parse(raw.toString('utf8'));
const N = closure.state_count;
if (!Number.isInteger(N) || !Array.isArray(closure.transitions) || closure.transitions.length !== N) throw new Error('invalid closure table');
for (let s = 0; s < N; s++) {
  if (!Array.isArray(closure.transitions[s]) || closure.transitions[s].length !== 9) throw new Error('invalid transition row ' + s);
  for (const t of closure.transitions[s]) if (!Number.isInteger(t) || t < 0 || t >= N) throw new Error('invalid transition target');
}
const key = xs => xs.join(',');
const maps = [Array.from({length:N}, (_, i) => i)];
const representatives = [[]];
const ids = new Map([[key(maps[0]), 0]]);
const transitions = [];
const levels = [1];
for (let h = 0; h < maps.length; h++) {
  const row = [];
  for (let a = 0; a < 9; a++) {
    const next = maps[h].map(s => closure.transitions[s][a]);
    const k = key(next);
    let id = ids.get(k);
    if (id === undefined) {
      id = maps.length;
      ids.set(k, id);
      maps.push(next);
      representatives.push(representatives[h].concat(a));
      const depth = representatives[id].length;
      levels[depth] = (levels[depth] || 0) + 1;
    }
    row.push(id);
  }
  transitions.push(row);
}
const rankDistribution = {};
const constantImages = [];
let idempotentCount = 0;
for (let i = 0; i < maps.length; i++) {
  const rank = new Set(maps[i]).size;
  rankDistribution[rank] = (rankDistribution[rank] || 0) + 1;
  if (rank === 1) constantImages.push(maps[i][0]);
  if (key(maps[i].map(s => maps[i][s])) === key(maps[i])) idempotentCount++;
}
const sourceBlobSha = crypto.createHash('sha1').update(Buffer.concat([Buffer.from('blob ' + raw.length + '\0'), raw])).digest('hex');
const result = {
  schema: 'bb6-paired-carry-transformation-monoid/v1',
  source: { path: sourcePath, git_blob_sha: sourceBlobSha },
  state_count: N,
  alphabet: Array.from({length:9}, (_, i) => String(Math.floor(i / 3)) + String(i % 3)),
  monoid_size: maps.length,
  max_shortest_representative_length: Math.max(...representatives.map(w => w.length)),
  shortest_representatives_by_length: levels,
  rank_distribution: rankDistribution,
  idempotent_count: idempotentCount,
  constant_transformation_count: constantImages.length,
  constant_transformation_images: constantImages,
  representatives,
  transformations: maps,
  transitions
};
fs.writeFileSync(outputPath, JSON.stringify(result, null, 2) + '\n');
console.log(JSON.stringify({monoid_size:result.monoid_size,levels:result.shortest_representatives_by_length,rank_distribution:result.rank_distribution,idempotent_count:result.idempotent_count,constant_transformation_count:result.constant_transformation_count}, null, 2));
