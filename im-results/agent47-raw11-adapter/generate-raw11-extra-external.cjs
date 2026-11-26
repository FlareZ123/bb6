'use strict';
// Generate the two Raw11-extra parent Covers whose only open leaves are
// discharged by the exact Root56 recurrence families in Raw11ExtraExternalLeaves.
const fs = require('node:fs');
const { search } = require('./generate-raw11-extra.cjs');
const { table, head, cert, slot, bit } = require('./generate-q0-lean.cjs');
const { sourceMitmCert } = require('../agent5-weighted-tnf-queue/q0-source-mitm-cert.cjs');
const { bank } = require('../agent5-weighted-tnf-queue/coarse-pair.cjs');
const route = require('./raw11-route.json');

const moves = Array.from('ABCDEF').flatMap(q =>
  Array.from('01').flatMap(w => Array.from('LR').map(d => w + d + q)));
const normalize = s => s.replaceAll('_', '');
const parse = s => normalize(s).match(/.{3}/g);
const size = t => 1 + (t[0] === 'h' ? t[3].reduce((n, k) => n + size(k), 0) : 0);
const split = (t, a, f) => t[3].map((k, j) => [
  k,
  a.map((s, i) => i === t[2] ? moves[j] : s),
  Math.max(f, 1 + (j >> 2))
]);
const hasExternal = t => t[0] === 'u' || (t[0] === 'h' && t[3].some(hasExternal));

const external = new Map([
  ['1RB1RD1RC0LD0LA0RE1LA1LB0RA0RF1LA---', {
    table: 'Raw11ExtraSweepCoverage.table false',
    proof: 'BB6.Agent47ExtraExternal.sweepSafe false'
  }],
  ['1RB1RD1RC0LD0LA0RE1LA1LB0RA0RF0RB---', {
    table: 'Raw11ExtraFamilyCoverage.variantTable 0',
    proof: 'BB6.Agent47ExtraExternal.familySafe 0'
  }],
  ['1RB1RD1RC0LD0LA0RE1LA1LB0RA0RF0RE---', {
    table: 'Raw11ExtraFamilyCoverage.variantTable 1',
    proof: 'BB6.Agent47ExtraExternal.familySafe 1'
  }],
  ['1RB1RD1RC0LD0LA0RE1LA1LB0RA1RF0RB---', {
    table: 'Raw11ExtraFamilyCoverage.variantTable 2',
    proof: 'BB6.Agent47ExtraExternal.familySafe 2'
  }],
  ['1RB1RD1RC0LD0LA0RE1LA1LB0RA1RF1RB---', {
    table: 'Raw11ExtraFamilyCoverage.variantTable 3',
    proof: 'BB6.Agent47ExtraExternal.familySafe 3'
  }],
  ['1RB1RD1RC0LD0LA0RE1LA1LB0RA1RF0RC---', {
    table: 'Raw11ExtraFamilyCoverage.variantTable 4',
    proof: 'BB6.Agent47ExtraExternal.familySafe 4'
  }],
  ['1RB1RD1RC0LD0LA0RE1LA1LB0RA1RF0LD---', {
    table: 'Raw11ExtraFamilyCoverage.variantTable 5',
    proof: 'BB6.Agent47ExtraExternal.familySafe 5'
  }],
  ['1RB1RD1RC0LD0LA1RE1LA1LB0LE0RF0RA---', {
    table: 'Raw11ExtraSweepCoverage.table true',
    proof: 'BB6.Agent47ExtraExternal.sweepSafe true'
  }]
]);

function collectWitnessOpen(t, out = []) {
  if (!Array.isArray(t)) return out;
  if (t[0] === 'u') out.push(normalize(t[1]));
  if (t[0] === 'b' && Array.isArray(t[3])) t[3].forEach(k => collectWitnessOpen(k, out));
  return out;
}

function emit(t, a, f, r) {
  switch (t[0]) {
    case 's':
      return `(.side ${t[2]} ${t[3]} ${bit(t[1] === 'R')} (${head(a, t[2]) + (t[1] === 'R' ? -t[4] : t[4])}))`;
    case 'p':
    case 'o': {
      const c = t[0] === 'p'
        ? sourceMitmCert(a.join(''), bank[t[1]], bank[t[2]])
        : r.openBank[a.join('')];
      if (!c) throw new Error('missing automata certificate for ' + a.join(''));
      return `(.automata ${cert(c)})`;
    }
    case 'h':
      if (!t[3].length) return `(.last ${t[1]} ${slot(t[2])})`;
      return `(split ${t[1]} ${slot(t[2])} ${f} #[\n${split(t, a, f).map(k => emit(k[0], k[1], k[2], r)).join(',\n')}])`;
    default:
      throw new Error('cannot emit node ' + t[0]);
  }
}

function generate(id) {
  const parentText = route.extra[id];
  if (typeof parentText !== 'string') throw new Error('missing Raw11 extra index ' + id);
  const witness = require(`../agent5-weighted-tnf-queue/raw11-extra-${id}-witness.json`);
  const witnessOpen = collectWitnessOpen(witness.tree).sort();
  const expected = [...external.keys()].filter(k =>
    (id === 92 ? k.includes('0LA0RE') : k.includes('0LA1RE'))).sort();
  if (JSON.stringify(witnessOpen) !== JSON.stringify(expected))
    throw new Error(`witness/external mismatch for ${id}: ${JSON.stringify({witnessOpen, expected})}`);

  const r = search(parentText, { retain: true });
  if (!r.tree || size(r.tree) !== r.n) throw new Error('incomplete retained search tree for ' + id);
  const opens = r.opens.map(normalize).sort();
  if (JSON.stringify(opens) !== JSON.stringify(expected))
    throw new Error(`search/witness open-leaf mismatch for ${id}: ${JSON.stringify({opens, expected})}`);

  const a = parse(parentText);
  const fresh = Math.max(...a.filter(x => x !== '---').map(x => x.charCodeAt(2) - 64));
  const B = r.bound;
  let out = `import PhaseTree
import Raw11ExtraExternalLeaves
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent47Extra${id}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := ${table(a)}
def bound : Nat := ${B}
`;

  function prove(t, current, f, p, name) {
    const suffix = name ? '_' + name : '';
    const safe = 'safe' + suffix;
    if (t[0] === 'u') {
      const ext = external.get(t[1]);
      if (!ext) throw new Error(`unmatched external leaf ${id}: ${t[1]}`);
      out += `theorem ${safe} : ∀ m, compatible ${p} m → WeightedBound ${B} m := by
  intro m hm
  have hEq : ${p} = ${ext.table} := by
    funext s
    rcases s with ⟨q,b⟩
    fin_cases q <;> cases b <;> rfl
  rw [hEq] at hm
  exact ${ext.proof} ${B} m hm
`;
      return;
    }
    if (size(t) <= 49 && !hasExternal(t)) {
      out += `def cert${suffix} : Tree := ${emit(t, current, f, r)}
theorem checked${suffix} : check ${B} ${p} cert${suffix} = true := by decide +kernel
theorem ${safe} : ∀ m, compatible ${p} m → WeightedBound ${B} m := sound ${B} _ cert${suffix} (by decide) checked${suffix}
`;
      return;
    }
    if (t[0] !== 'h' || !t[3].length) throw new Error('expected split containing an external leaf at ' + id);
    const kids = split(t, current, f);
    for (let j = 0; j < kids.length; j++) {
      const [child, childTable, childFresh] = kids[j];
      const childName = name ? `${name}_${j}` : String(j);
      const childParent = 'p_' + childName;
      out += `def ${childParent} := refine ${p} ${slot(t[2])} (some ${move(j)})
`;
      prove(child, childTable, childFresh, childParent, childName);
    }
    out += `theorem ${safe} : ∀ m, compatible ${p} m → WeightedBound ${B} m := by
  apply split_safe ${B} ${p} ${t[1]} ${slot(t[2])} ${f} (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | ${kids.map((_, j) => 'exact safe_' + (name ? `${name}_${j}` : String(j))).join(' | ')} | omega
`;
  }

  prove(r.tree, a, fresh, 'parent', '');
  out += `theorem cover : Cover (WeightedBound bound) parent := .leaf _ (by
  intro m hm
  simpa only [bound] using safe m hm)
#print axioms cover
end BB6.Agent47Extra${id}
`;
  return {
    id, table: parentText, nodes: r.n, bound: B, stats: r.stats,
    openLeaves: opens, source: out
  };
}

if (require.main === module) {
  const results = [92, 124].map(generate);
  for (const r of results)
    fs.writeFileSync(`Raw11Extra${r.id}.lean`, r.source);
  fs.writeFileSync('raw11-extra-external-manifest.json',
    JSON.stringify(results.map(({source, ...r}) => r), null, 2) + '\n');
  console.log(JSON.stringify(results.map(({source, ...r}) => r)));
}

module.exports = { generate };
