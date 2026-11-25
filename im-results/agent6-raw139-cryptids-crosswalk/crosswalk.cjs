'use strict';
const fs = require('node:fs');
const path = require('node:path');
const root = path.resolve(__dirname, '..', '..');
const witnessPath = path.join(root, 'im-results', 'agent41-raw139-small', 'witness-data.json');
const manifestPath = path.join(__dirname, 'cryptids-191-manifest.tsv');
const witness = JSON.parse(fs.readFileSync(witnessPath, 'utf8'));
const rows = fs.readFileSync(manifestPath, 'utf8').trim().split(/\r?\n/).slice(1);
const modules = rows.map(line => {
  const [status, rle, modulePath, blob] = line.split('\t');
  return {status, rle, path: modulePath, blob};
});
const letters = 'ABCDEF';
function permutations(xs) {
  if (!xs.length) return [''];
  return [...xs].flatMap((x, i) =>
    permutations(xs.slice(0, i) + xs.slice(i + 1)).map(t => x + t));
}
const statePermutations = permutations('BCDEF').map(s => 'A' + s);
function parseRle(rle) {
  const slots = rle.split('_').flatMap(pair => [pair.slice(0, 3), pair.slice(3)]);
  if (slots.length !== 12) throw new Error('bad RLE: ' + rle);
  return slots.map(x => x === '---' ? null : x);
}
function transform(table, permutation, reflect) {
  const out = Array(12);
  for (let q = 0; q < 6; q++) for (let bit = 0; bit < 2; bit++) {
    const move = table[2 * q + bit];
    const destination = 2 * letters.indexOf(permutation[q]) + bit;
    out[destination] = move === null ? null
      : move[0] + (reflect ? (move[1] === 'R' ? 'L' : 'R') : move[1])
        + permutation[letters.indexOf(move[2])];
  }
  return out;
}
function slotName(i) { return letters[Math.floor(i / 2)] + (i % 2); }
function firstErasedQuery(source, target, limit = 1000) {
  const ones = new Set();
  let q = 0, head = 0;
  const prior = [];
  const seen = new Set();
  for (let time = 0; time < limit; time++) {
    const bit = ones.has(head) ? 1 : 0;
    const slot = 2 * q + bit;
    const label = slotName(slot);
    if (target[slot] === null)
      return {time, slot: label, sourceMove: source[slot] || '---', priorFirstUses: prior};
    if (!seen.has(slot)) { seen.add(slot); prior.push(label + '@' + time); }
    const move = source[slot];
    if (move === null)
      return {time, slot: label, sourceMove: '---', priorFirstUses: prior,
        sourceHaltsOnAssignedSlot: true};
    if (move[0] === '1') ones.add(head); else ones.delete(head);
    head += move[1] === 'R' ? 1 : -1;
    q = letters.indexOf(move[2]);
  }
  return {notVisitedWithin: limit, priorFirstUses: prior};
}
if (modules.length !== 191 ||
    modules.filter(m => m.status === 'NonHalt').length !== 159 ||
    modules.filter(m => m.status === 'Halt').length !== 32)
  throw new Error('unexpected pinned Cryptids module inventory');
if (statePermutations.length !== 120) throw new Error('permutation enumeration failed');
if (witness.residuals.length !== 81) throw new Error('raw139 residual list changed; review the source first');
const results = [];
for (const leaf of witness.residuals) {
  const target = parseRle(leaf.table);
  const found = [];
  for (const mod of modules) {
    const source = parseRle(mod.rle);
    if (source.filter(x => x === null).length !== 1)
      throw new Error('source table must have exactly one HHH: ' + mod.path);
    for (const permutation of statePermutations) for (const reflected of [false, true]) {
      const transformed = transform(source, permutation, reflected);
      if (!target.every((x, i) => x === null || x === transformed[i])) continue;
      const holes = target.map((x, i) => x === null ? i : -1).filter(i => i >= 0);
      let transfer, erased;
      if (holes.length === 1 && transformed[holes[0]] === null) {
        transfer = 'direct-one-hole: only erased slot is source HHH; IsNotHalt rules out querying it';
        erased = {slot: slotName(holes[0]), time: 'never (by source IsNotHalt)'};
      } else {
        erased = firstErasedQuery(transformed, target);
        transfer = erased.time !== undefined
          ? 'not-direct: source first queries an additional erased row'
          : 'unresolved: no erased-row query found within finite replay';
      }
      found.push({...mod, permutation, reflected, sourceHaltSlot: slotName(transformed.findIndex(x => x === null)),
        transfer, erased});
    }
  }
  if (found.length) results.push({leaf, found});
}
const matches = results.flatMap(({leaf, found}) => found.map(m => ({
  candidate_rle: leaf.table, address: leaf.address.join('>'), holes: leaf.holes,
  source_status: m.status, source_rle: m.rle, module_path: m.path, blob_sha: m.blob,
  state_permutation: m.permutation, reflected: m.reflected,
  transfer_assessment: m.transfer, first_erased_slot: m.erased.slot || '-',
  first_erased_time: m.erased.time || '-', first_erased_source_move: m.erased.sourceMove || '-',
  prior_first_uses: (m.erased.priorFirstUses || []).join(',')
})));
const expected = [
  '1RB---_1RC---_1LD---_---0LE_---1LF_0LD---',
  '1RB---_1RC---_1LD---_---0LE_---1LF_1LA---',
  '1RB0LE_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LD---'
];
if (matches.length !== 3 || !expected.every(r => matches.some(m => m.candidate_rle === r)))
  throw new Error('crosswalk result changed; inspect before updating the report');
console.log('Cryptids commit: 3647718b5df22e1a61462dec0376bd204526285a');
console.log('Source modules: ' + modules.length + ' (159 NonHalt, 32 Halt)');
console.log('Transforms per source: ' + (statePermutations.length * 2) + ' (120 A-fixing state permutations x 2 tape orientations)');
console.log('Raw139 candidate residuals: ' + witness.residuals.length);
console.log('Compatibility matches: ' + matches.length);
for (const m of matches) {
  console.log([m.source_status, m.candidate_rle, m.module_path,
    m.state_permutation, m.reflected, m.transfer_assessment,
    m.first_erased_slot, m.first_erased_time].join('\t'));
}
