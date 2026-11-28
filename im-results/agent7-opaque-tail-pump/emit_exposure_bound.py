#!/usr/bin/env python3
"""Emit transport of an exact blank-exposure theorem to a universal weighted bound.

Requires source-checked reached/hole from exposure_emit.py, and original
Run0ExposureBound.zipRead_of_run0 and bounded_of_query. All kernel checked.
"""
import json,sys
from pathlib import Path

def main(info_path,out):
    d=json.loads(Path(info_path).read_text())
    assert d['slot'] in ('F0','B1'),d
    assert d['undefined_after'] in (23126,60671),d
    n=d['undefined_after']; b=n+6
    q=ord(d['slot'][0])-65; a='true' if d['slot'][1]=='1' else 'false'
    srcns=d['namespace']
    assert srcns.startswith('BB6.Agent7D100Exposure')
    source=f'''import Raw36D100Exposure
import Run0ExposureBound
import FastZipWeight
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7D100ExposureBound
open BB6Coverage BB6Coverage.Agent10ZipAudit
open BB6.Agent13BlankDelay BB6.Agent31ThreeHole
open BB6.Agent50TNFPilot BB6.Agent7D100ExposureBridge
open BB6.Agent29FastZipWeight
open {srcns}
theorem hroot : table initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem hno : weightedTNFNoAssignedHalt table := by decide
theorem query : zipRead table {n} = some ({q},{a}) := by
  exact zipRead_of_run0 table {n} _ reached
theorem hrest : restOK table ({q},{a}) = true := by decide
theorem hweight : weightOK table ({q},{a}) {n} {b} = true :=
  weightOK_of_slack table ({q},{a}) {n} {b} (by omega)
theorem bound (m : Machine) (hm : compatible table m) : WeightedBound {b} m :=
  bounded_of_query table {n} {b} ({q},{a})
    query hroot hno hole hweight hrest m hm
#print axioms bound
end BB6.Agent7D100ExposureBound
'''
    Path(out).write_text(source)
    print(f'Generated kernel-checkable weighted-bound candidate {b} at {d["slot"]}')
if __name__=='__main__':
    main(sys.argv[1],sys.argv[2])
