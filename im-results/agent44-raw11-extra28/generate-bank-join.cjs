'use strict';
// Alternative to the proof-dependent Route 158 final constructor.
// Every finite-bank certificate is exact table-checked using sameTable_sound;
// the final theorem assumes no oracle and leaves no unresolved child.
const fs=require('node:fs'),path=require('node:path');
const children=[
  [7,true,true,1,72,'Raw11Extra28M7Join','BB6.Agent44Extra28M7','parent','safe'],
  [8,false,false,2,42,'Raw11Extra28D1LCJoin','BB6.Agent44Extra28D1LC','parent','safe'],
  [9,false,true,2,84,'Raw11Extra28M9Join','BB6.Agent44Extra28M9','parent','safe'],
  [10,true,false,2,101,'Raw11Extra28M10Join','BB6.Agent44Extra28M10','parent','safe'],
  [12,false,false,3,64,'Raw11Extra28LDJoin','BB6.Agent44Extra28LD','parent','safe'],
  [13,false,true,3,79,'Raw11Extra28M13Join','BB6.Agent44Extra28M13','parent','safe'],
  [14,true,false,3,96,'Raw11Extra28M14Join','BB6.Agent44Extra28M14','parent','safe'],
  [15,true,true,3,119,'Raw11Extra28M15Join','BB6.Agent44Extra28M15','parent','safe'],
  [16,false,false,4,81,'Raw11Extra28M16Join','BB6.Agent44Extra28M16','parent','safe'],
  [17,false,true,4,150,'FastRaw11M17Join','BB6.Agent44FastM17','p_root','safe_root'],
  [18,true,false,4,141,'FastRaw11M18Join','BB6.Agent44FastM18','p_root','safe_root'],
  [19,true,true,4,158,'FastRaw11M19Join','BB6.Agent44FastM19','p_root','safe_root']
];
const bit=b=>b?'true':'false';
const term=x=>'refine BB6.Agent44Extra28AllChildren.parent (3,true) (some ⟨'+bit(x[1])+','+bit(x[2])+','+x[3]+'⟩)';
const src=[
 'import Raw11Extra28CodeBank',
 'import FastKey',
 ...children.map(c=>'import '+c[5]),
 'set_option maxRecDepth 100000',
 'set_option maxHeartbeats 0',
 'namespace BB6.Agent44Extra28BankCompleted',
 'open BB6Coverage BB6.Agent13BlankDelay',
 ...children.flatMap(c=>[
 'private def child'+c[0]+' : PartialMachine := '+term(c),
 'theorem exact'+c[0]+' : child'+c[0]+' = '+c[6]+'.'+c[7]+' :=\n  BB6.Agent47PhaseFrontier.sameTable_sound (by decide +kernel)',
 'private theorem bounded'+c[0]+' : ∀ m, compatible child'+c[0]+' m → WeightedBound 158 m := by\n  intro m hm\n  rw [exact'+c[0]+'] at hm\n  exact liftBound (by decide : '+c[4]+' ≤ 158) ('+c[6]+'.'+c[8]+' m hm)'
 ]),
 '',
 'def bank : BB6.Agent44Extra28CodeBank.CertificateBank 158 := [',
 children.map(c=>'  ⟨child'+c[0]+', bounded'+c[0]+'⟩').join(',\n'),
 ']',
 '',
 'theorem covers_all_keys : ∀ k ∈ BB6.Agent44Extra28AllChildren.remaining.map BB6.Agent50FastKey.tableCode,',
 '    k ∈ bank.map (fun e => BB6.Agent50FastKey.tableCode e.val) := by decide +kernel',
 '',
 'theorem literal_complete : Cover (WeightedBound 158) BB6.Agent44Extra28AllChildren.parent :=',
 '  BB6.Agent44Extra28CodeBank.consume_bank 158 (by decide)',
 '    BB6.Agent50FastKey.tableCode',
 '    (fun _ _ h => BB6.Agent50FastKey.tableCode_inj h)',
 '    bank covers_all_keys',
 '',
 '#print axioms covers_all_keys',
 '#print axioms literal_complete',
 'end BB6.Agent44Extra28BankCompleted',
 ''
].join('\n');
const output=process.argv[2]||path.join(process.cwd(),'Raw11Extra28LiteralBank.lean');
fs.writeFileSync(output,src);
console.log('exact-bank Lean source written '+output+' with '+children.length+' original child proofs');
