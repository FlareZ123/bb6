"""Emit exact last-hole bounds from already checked packed-sweep read theorems.
The delay choices are untrusted inputs; Lean checks realizability and maximality.
"""
import json, sys
from pathlib import Path
src=Path(sys.argv[1]);out=Path(sys.argv[2]);out.mkdir(exist_ok=True,parents=True)
r=json.loads((src/'recipes.json').read_text());p=json.loads((src/'partition.json').read_text())['open']
delays={117:1,507:1,744:1,2937:1,3158:2,3546:1}
for i,v in r.items():
    if v[0]!='late' or v[1]<1000:continue
    i=int(i);n=v[1];d=delays.get(i,0);t=p[i];assert t.count(24)==1;s=t.index(24);slot=f'({s//2},{str(bool(s%2)).lower()})';b=n+d+1
    content=f'''import OneLCSweep{i}
import OneLCExactLast
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace BB6.Agent4E0OneLCLate.H{i}Sweep
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot BB6.Agent4E0OneLCLate

theorem exactResult : Cover (WeightedBound {b}) p ∧
    (∀ B, Cover (WeightedBound B) p → {b} ≤ B) ∧
    (∃ m : Machine, HaltsAfter m {b-1}) :=
  exact_last p {n} {d} {slot} read (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
#print axioms exactResult
end BB6.Agent4E0OneLCLate.H{i}Sweep
'''
    (out/f'OneLCExact{i}.lean').write_text(content)
