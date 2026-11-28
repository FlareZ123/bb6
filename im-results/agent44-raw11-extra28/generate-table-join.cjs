'use strict';
// Generates an exact original-table parent theorem without proof-dependent
// computation. Uses the source-accepted static 12-table complement checker
// and the separately accepted twelve original child Covers.
const fs=require('node:fs'),path=require('node:path');
const children=[
  [7,72,'Raw11Extra28M7Join','BB6.Agent44Extra28M7','parent','safe'],
  [8,42,'Raw11Extra28D1LCJoin','BB6.Agent44Extra28D1LC','parent','safe'],
  [9,84,'Raw11Extra28M9Join','BB6.Agent44Extra28M9','parent','safe'],
  [10,101,'Raw11Extra28M10Join','BB6.Agent44Extra28M10','parent','safe'],
  [12,64,'Raw11Extra28LDJoin','BB6.Agent44Extra28LD','parent','safe'],
  [13,79,'Raw11Extra28M13Join','BB6.Agent44Extra28M13','parent','safe'],
  [14,96,'Raw11Extra28M14Join','BB6.Agent44Extra28M14','parent','safe'],
  [15,119,'Raw11Extra28M15Join','BB6.Agent44Extra28M15','parent','safe'],
  [16,81,'Raw11Extra28M16Join','BB6.Agent44Extra28M16','parent','safe'],
  [17,150,'FastRaw11M17Join','BB6.Agent44FastM17','p_root','safe_root'],
  [18,141,'FastRaw11M18Join','BB6.Agent44FastM18','p_root','safe_root'],
  [19,158,'FastRaw11M19Join','BB6.Agent44FastM19','p_root','safe_root']
];
const base='BB6.Agent44Extra28FromCovers';
const src=[
 'import Raw11Extra28FromCovers',
 ...children.map(c=>'import '+c[2]),
 'set_option maxRecDepth 100000',
 'set_option maxHeartbeats 0',
 'namespace BB6.Agent44Extra28TableCompleted',
 'open BB6Coverage BB6.Agent13BlankDelay',
 ...children.map(c=>'theorem exact'+c[0]+' : '+base+'.p'+c[0]+' = '+c[3]+'.'+c[4]+' :=\n  BB6.Agent47PhaseFrontier.sameTable_sound (by decide +kernel)'),
 '',
 'def covers : '+base+'.Covers := {',
 children.map(c=>'  c'+c[0]+' := .leaf _ (by\n    intro m hm\n    rw [exact'+c[0]+'] at hm\n    exact '+c[3]+'.'+c[5]+' m hm)').join(',\n'),
 '}',
 '',
 'theorem literal_complete : Cover (WeightedBound 158) BB6.Agent44Extra28AllChildren.parent :=',
 '  '+base+'.completeCover covers',
 '',
 'theorem literal_complete_at (B : Nat) (hB : 158 ≤ B) :',
 '    Cover (WeightedBound B) BB6.Agent44Extra28AllChildren.parent :=',
 '  '+base+'.completeCoverAt B hB covers',
 '',
 '#print axioms literal_complete',
 '#print axioms literal_complete_at',
 'end BB6.Agent44Extra28TableCompleted',
 ''
].join('\n');
const out=process.argv[2]||path.join(process.cwd(),'Raw11Extra28LiteralTable.lean');
fs.writeFileSync(out,src);
console.log('created '+out+' with '+children.length+' exact original-source child Covers');
