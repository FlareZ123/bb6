'use strict';

/**
 * Original-source-focused, axiom-free Coq compilation reduction.
 *
 * Run ONLY inside a checkout of ccz181078/busycoq pinned at
 * 33209bc7dc282b38c8cd6be507bfc551fea56108.
 *
 * The original TM7.halt theorem and its upstream proof dependencies remain
 * byte-identical within their enclosing module. Remove computations only for
 * the three unrelated blank-start halting theorems of TM9, TM6 and TM8.
 * No "Admitted", "Axiom", substitute theorem, or modified TM7 proof is used.
 *
 * Derived source is NOT a verbatim upstream recompilation. The modification
 * is transparent and is only intended to independently verify TM7.halt and
 * the separate original-row311 mirror bridge in a resource-bounded job.
 */
const fs = require('node:fs');
const path = require('node:path');
const crypto = require('node:crypto');
const assert = require('node:assert/strict');

const cwd = process.cwd();
const v3Path = path.join(cwd, 'Others_v3.v');
const bridgePath = path.join(cwd, 'Agent46OriginalRootMirror.v');

/** @param {Buffer} bytes */
function shaGitBlob(bytes) {
  return crypto.createHash('sha1').update(Buffer.from('blob ' + bytes.length + '\0')).update(bytes).digest('hex');
}

/** @param {string} file @param {string} contents */
function atomicWrite(file, contents) {
  const lock = file + '.agent46.lock';
  const fd = fs.openSync(lock, 'wx');
  const temp = file + '.agent46.tmp';
  try {
    fs.writeFileSync(temp, contents, {flag:'wx'});
    fs.renameSync(temp, file);
  } finally {
    fs.closeSync(fd);
    if (fs.existsSync(temp)) fs.unlinkSync(temp);
    fs.unlinkSync(lock);
  }
}

/** @param {string} src @param {string} name */
function moduleSpan(src, name) {
  const start = src.indexOf('Module ' + name + '.');
  assert(start >= 0, 'missing original module ' + name);
  const end = src.indexOf('End ' + name + '.', start);
  assert(end > start, 'missing source module end ' + name);
  return {start, end};
}

let v3 = fs.readFileSync(v3Path);
assert.equal(shaGitBlob(v3), 'ab372a2521d386c39ce68e57baa5d6d52d1f49d0',
  'expected exact upstream original Others_v3.v Git blob before reduction');
v3 = v3.toString('utf8');
const targetModule = moduleSpan(v3, 'TM7');
const exactTargetBytes = v3.slice(targetModule.start, targetModule.end);
assert.match(exactTargetBytes, /Theorem halt:\s*halts tm c0\.\s*Proof\.\s*apply \(from_check 1000000000%N\)\. native_check_eq\. Time Qed\./);
const expectedProofs = [
  ['TM9', 'Proof. apply (@check_spec 1000000000%N A). native_check_eq. Time Qed.'],
  ['TM6', 'Proof. apply (from_check 1000000000%N). native_check_eq. Time Qed.'],
  ['TM8', 'Proof. apply (from_check 1000000000%N). native_check_eq. Time Qed.']
];
for (const [name, proof] of expectedProofs) {
  const {start,end} = moduleSpan(v3, name);
  const before = v3.slice(start, end);
  const theorem = 'Theorem halt: halts tm c0.\n' + proof;
  assert.equal(before.split(theorem).length, 2, 'unexpected or missing unrelated theorem proof: ' + name);
  const after = before.replace(theorem, '(* Original ' + name + '.halt omitted from TARGETED verification: never used to derive TM7.halt. *)');
  v3 = v3.slice(0,start) + after + v3.slice(end);
  const printer = 'Print Assumptions ' + name + '.halt.';
  assert(v3.includes(printer), 'missing original assumption command for ' + name);
  v3 = v3.replace(printer, '(* Original ' + name + '.halt assumption command omitted; theorem not built. *)');
}
const finalTargetSpan = moduleSpan(v3, 'TM7');
assert.equal(v3.slice(finalTargetSpan.start, finalTargetSpan.end), exactTargetBytes,
  'TARGET TM7 proof or its module changed unexpectedly');
assert(!/\b(?:Admitted|Axiom)\s+/.test(v3), 'proof escape prohibited in derived source');
atomicWrite(v3Path, v3);
console.log('TARGETED source generated; original TM7 module strictly byte-identical, other three expensive halt proofs omitted without axioms');

let bridge = fs.readFileSync(bridgePath, 'utf8');
const bStart = bridge.indexOf('Module OctoberMirror6.');
const bEnd = bridge.indexOf('End OctoberMirror6.', bStart);
assert(bStart >= 0 && bEnd > bStart);
const exactBridge = bridge.slice(
  bridge.indexOf('Module OctoberRoot311.'),
  bridge.indexOf('End OctoberRoot311.') + 'End OctoberRoot311.'.length);
assert.match(exactBridge, /Theorem halts:\s*halts tm c0\./);
bridge = bridge.slice(0,bStart) + '(* Independent mirror6 source not verified by targeted root311 run. *)\n' +
  bridge.slice(bEnd + 'End OctoberMirror6.'.length);
bridge = bridge.replace('Print Assumptions OctoberMirror6.halts.',
  '(* Omitted unrelated OctMirror6 proof from targeted compilation. *)');
assert(bridge.includes(exactBridge), 'target original root bridge changed');
assert(!/\b(?:Admitted|Axiom)\s+/.test(bridge), 'no proof escape in targeted bridge');
atomicWrite(bridgePath, bridge);
console.log('TARGETED bridge generated: exact original-root311 Coq theorem and exact-n count-transfer proof unchanged');
