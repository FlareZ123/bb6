// Emit original-source direct finite-stack certificates, without MITM search.
const fs = require('node:fs');
const certs = require('./q0-open-automata.json');
const list = xs => '['+xs.join(';')+']';
const edge = ([a,i]) => '(S'+a+','+i+')';
const stack = s => '(Build_auto_stack '+list(s.pop.map(es=>list(es.map(edge))))+' '+list(s.push.map(([a,b])=>'('+a+','+b+')'))+')';
const table = s => s.match(/.{6}/g).join('_');
const cert = c => 'Build_auto_cert '+stack(c.left)+' '+stack(c.right)+' '+list(c.rows.map(([q,s,i,j])=>'('+'ABCDEF'[q]+',S'+s+','+i+','+j+')'));
const prefix = 'From BusyCoq Require Import Agent5SourceAutomata Individual62 Enumerate62.\nFrom Coq Require Import List String.\nImport ListNotations TNF_Node.\nOpen Scope string_scope.\nOpen Scope nat_scope.\n';
const selected = Object.entries(certs).filter(([id])=>!process.argv[3] || id.startsWith(process.argv[3]));
if (!selected.length) throw Error('No selected certificates');
let out=prefix;
for (const [id,c] of selected) {
 out += 'Definition p_'+id+' := TM_from_str "'+table(c.table)+'".\n';
 out += 'Definition cert_'+id+' : auto_cert := '+cert(c)+'.\n';
 out += 'Lemma checked_'+id+' : auto_cert_check p_'+id+' cert_'+id+' = true. Proof. vm_compute. reflexivity. Qed.\n';
 out += 'Theorem nonhalt_'+id+' : ~ halts p_'+id+' c0. Proof. exact (auto_cert_nonhalt _ _ checked_'+id+'). Qed.\n';
}
out+='Print Assumptions nonhalt_'+selected.at(-1)[0]+'.\n';
fs.writeFileSync(process.argv[2],out);
console.log('generated '+selected.length+' direct certificates');
