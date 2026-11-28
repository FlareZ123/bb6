'use strict';
// Generates an axiom-auditable original-source Full Extra28 parent theorem.
// Does not generate or assume any child certificate. The caller supplies
// twelve independently kernel-accepted imported modules.
const fs = require('node:fs'), path = require('node:path');
const children = [
  [7, true, true, 1, 72, 'Raw11Extra28M7Join','BB6.Agent44Extra28M7','parent','safe'],
  [8, false,false,2, 42, 'Raw11Extra28D1LCJoin','BB6.Agent44Extra28D1LC','parent','safe'],
  [9, false,true, 2, 84, 'Raw11Extra28M9Join','BB6.Agent44Extra28M9','parent','safe'],
  [10,true, false,2,101, 'Raw11Extra28M10Join','BB6.Agent44Extra28M10','parent','safe'],
  [12,false,false,3, 64, 'Raw11Extra28LDJoin','BB6.Agent44Extra28LD','parent','safe'],
  [13,false,true, 3, 79, 'Raw11Extra28M13Join','BB6.Agent44Extra28M13','parent','safe'],
  [14,true, false,3, 96, 'Raw11Extra28M14Join','BB6.Agent44Extra28M14','parent','safe'],
  [15,true, true, 3,119, 'Raw11Extra28M15Join','BB6.Agent44Extra28M15','parent','safe'],
  [16,false,false,4, 81, 'Raw11Extra28M16Join','BB6.Agent44Extra28M16','parent','safe'],
  [17,false,true, 4,150, 'FastRaw11M17Join','BB6.Agent44FastM17','p_root','safe_root'],
  [18,true, false,4,141, 'FastRaw11M18Join','BB6.Agent44FastM18','p_root','safe_root'],
  [19,true, true, 4,158, 'FastRaw11M19Join','BB6.Agent44FastM19','p_root','safe_root']
];
const bool = b => b ? 'true' : 'false';
const term = x => `refine BB6.Agent44Extra28AllChildren.parent (3,true) (some ⟨${bool(x[1])},${bool(x[2])},${x[3]}⟩)`;
const source = [
  'import Raw11Extra28CompleteJoin',
  ...[...new Set(children.map(x => x[5]))].map(x => 'import ' + x),
  'set_option maxRecDepth 100000',
  'set_option maxHeartbeats 0',
  'namespace BB6.Agent44Extra28Completed',
  'open BB6Coverage BB6.Agent13BlankDelay',
  '/-- All imported child tables must match the literal first-D1 successors. -/',
  ...children.map(x => `theorem exact${x[0]} : ${term(x)} = ${x[6]}.${x[7]} :=`+
    '\n  BB6.Agent47PhaseFrontier.sameTable_sound (by decide +kernel)'),
  '',
  'def certificates : BB6.Agent44Extra28CompleteJoin.Certificates := {',
  children.map(x => `  c${x[0]} := by\n    intro m hm\n    change compatible (${term(x)}) m at hm\n    rw [exact${x[0]}] at hm\n    exact ${x[6]}.${x[8]} m hm`).join(',\n'),
  '}',
  '',
  'theorem literal_complete :',
  '    Cover (WeightedBound 158) BB6.Agent44Extra28AllChildren.parent :=',
  '  BB6.Agent44Extra28CompleteJoin.completeCover certificates',
  '',
  'theorem literal_complete_at (B : Nat) (hB : 158 ≤ B) :',
  '    Cover (WeightedBound B) BB6.Agent44Extra28AllChildren.parent :=',
  '  BB6.Agent44Extra28CompleteJoin.completeCoverAt B hB certificates',
  '',
  '#print axioms literal_complete',
  '#print axioms literal_complete_at',
  'end BB6.Agent44Extra28Completed',
  ''
].join('\n');
const out = process.argv[2] || path.join(process.cwd(), 'Raw11Extra28LiteralComplete.lean');
fs.writeFileSync(out, source);
console.log('created ' + out + ' with ' + children.length + ' exact source child bindings');
