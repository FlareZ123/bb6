#!/usr/bin/env node
/**
 * Source-linked Raw34 exact physical-table coverage frontier.
 *
 * Each of the four inputs is an exact 25-outcome symbolic-cylinder audit,
 * executed independently.  We combine (i) all-time nonhalting certificates
 * based on the 3,087 old cylinders + ten closed-state masks + the disjoint
 * E/F binary-odometer sources, (ii) Agent23's D1=1RD disjoint extra bank,
 * and (iii) genuine early-halting cylinders with D1 != 1RD.
 *
 * Nonhalting and genuine halting sets are disjoint by determinism; Agent23
 * versus our 1,067 halters are disjoint already at literal D1. The source
 * Raw34EarlyHaltersSound proves genuine halts (stronger than WeightedBound).
 * This finite counting script is not a Lean cardinality theorem.
 */
import assert from "node:assert/strict";
import {spawnSync} from "node:child_process";
import {join,dirname} from "node:path";
import {fileURLToPath} from "node:url";
const root=dirname(fileURLToPath(import.meta.url));
function read(file){
 const p=spawnSync(process.execPath,[join(root,file)],{
   encoding:"utf8",timeout:120000,maxBuffer:8*1024*1024
 });
 if(p.status!==0)throw new Error(file+": "+p.stderr);
 return JSON.parse(p.stdout);
}
const graph=read("audit_closed_graph_ten.mjs");
const binary=read("audit_binary_pair_ten.mjs");
const early=read("audit_halt8.mjs");
const late=read("audit_halt9_increment.mjs");
const N=25n**8n;
const get=(x,k)=>BigInt(x[k]);
assert.equal(N,152587890625n);
assert.equal(get(graph,"combinedNonhaltingMassIfAccepted"),135375687648n);
assert.equal(get(binary,"oldNineGraphNonhalt"),get(graph,"combinedNonhaltingMassIfAccepted"));
assert.equal(get(binary,"freshAcrossBothIfSourcesAccepted"),1638746n);
assert.equal(binary.disjointAtD1,true);
assert.equal(get(binary,"nonhaltUnionWithBothIfAccepted"),
  get(graph,"combinedNonhaltingMassIfAccepted")+get(binary,"freshAcrossBothIfSourcesAccepted"));
assert.equal(get(binary,"knownClassificationWithAgent23IfAccepted"),
  get(binary,"nonhaltUnionWithBothIfAccepted")+get(graph,"agent23IncrementBeyondOldTen"));
assert.equal(get(graph,"D1_1RD_newestAgent23"),5993118083n);
assert.equal(early.witnessCount,109);
assert.equal(late.existingHalt8,109);
assert.equal(late.additionalHalt9,958);
assert.equal(get(early,"totalHaltingPhysical"),9970703125n);
assert.equal(get(late,"additionalHalt9Physical"),1105468750n);
assert.equal(get(late,"totalHalt8PlusHalt9Physical"),
  get(early,"totalHaltingPhysical")+get(late,"additionalHalt9Physical"));
const nonhalt=get(binary,"nonhaltUnionWithBothIfAccepted");
const d1extra=get(graph,"agent23IncrementBeyondOldTen");
const halters=get(late,"totalHalt8PlusHalt9Physical");
const proved=nonhalt+d1extra+halters;
assert.equal(proved,147005580724n);
const residual=N-proved;
assert.equal(residual,5582309901n);
const physicalNonD1=24n*(25n**7n);
assert(halters<physicalNonD1);
console.log(JSON.stringify({
  status:"Exact source-linked 25-ary physical union and complement, not a Lean global Cover",
  root:"1RB---_1RC---_0RD---_1LC---_------_------",
  sourceNonhaltWithoutOdometers:String(get(graph,"combinedNonhaltingMassIfAccepted")),
  EandFSourceOdometerNew:String(get(binary,"freshAcrossBothIfSourcesAccepted")),
  sourceNonhaltWithOdometers:String(nonhalt),
  newAgent23_D1_1RD_BeyondNonhaltBank:String(d1extra),
  shortHalterWitnesses:early.witnessCount+late.additionalHalt9,
  actualHalting_UnderNineQueries_D1OtherThan1RD:String(halters),
  knownSourceCertificateUnion:String(proved),
  notYetCoveredByTheseCertificates:String(residual),
  parentPhysicalTotal:String(N),
  importantBoundary:"Source gate for strengthened halter proof plus original theorem checks; combinatorial union not kernel checked",
  sources:[
    "BB6.Agent40Raw34GraphClosed.never_of_mask",
    "BB6.Agent40Raw34BinaryCounter.all_time_never",
    "BB6.Agent40Raw34BinaryCounterF.all_time_never",
    "BB6.Agent40Raw34EarlyHalters.all_bank8_halt",
    "BB6.Agent40Raw34EarlyHalters.all_bank9_halt",
    "BB6.Agent23Raw34Next.check_sound"
  ]
},null,2));
