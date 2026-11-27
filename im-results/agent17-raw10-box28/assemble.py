#!/usr/bin/env python3
"""Join only named source theorems. No numeric counts or discovery rows certify a cut.
Manifest entries: {"d0":14,"code":18,"bound":3640,"module":"Box28D18Closure",
"theorem":"BB6.Agent13.Box28D18.sourceBound","domain":"BB6.Agent13.Box28D18.sourceDomain"}.
Output remains conditional on unproved cut keys. If all 118 keys present, emit unconditional bound.
"""
import argparse,json
from pathlib import Path
from cuts import TODO,stem
p=argparse.ArgumentParser()
p.add_argument('manifest',type=Path)
p.add_argument('out',type=Path)
a=p.parse_args()
entries=sorted(json.loads(a.manifest.read_text()),key=lambda x:(x['d0'],x['code']))
keys=[(x['d0'],x['code']) for x in entries]
canon={(d,v) for d,vs in TODO.items() for v in vs}
assert len(canon)==118 and len(keys)==len(set(keys)) and set(keys)<=canon
B=max([11]+[x['bound'] for x in entries])
s=['import Box28Join',*(f"import {x}" for x in sorted({x['module'] for x in entries})),
'set_option maxRecDepth 100000','set_option maxHeartbeats 0',
'namespace BB6.Agent17.Box28Assembled',
'open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box BB6.Agent49BoxBridge',
'open BB6.Agent17.Box28Join',
'def accepted : List Key := ['+','.join(f'({d},{v})' for d,v in keys)+']',
'def residual : List Key := canonical.filter (fun p => !accepted.contains p)',
f'theorem residual_count : residual.length = {len(canon)-len(keys)} := by decide']
for x in entries:
    d,v=x['d0'],x['code']
    k=f'd{d}v{v}'
    s += [f'theorem {k} : Good {B} ({d},{v}) := by',
          f'  apply good_mono {x["bound"]} {B} (by decide)',
          '  intro m hm',
          f'  exact {x["theorem"]} m hm']
if entries:
    s += [f'theorem accepted_good : ∀ p ∈ accepted, Good {B} p := by',
           '  intro p hp','  simp only [accepted,List.mem_cons,List.not_mem_nil,or_false] at hp',
           '  rcases hp with '+'|'.join(['h']*len(keys))+' <;> subst p']
    s += [f'  · exact d{d}v{v}' for d,v in keys]
else:
    s += [f'theorem accepted_good : ∀ p ∈ accepted, Good {B} p := by simp [accepted]']
s += [f'theorem parent_bound (h : ∀ p ∈ residual, Good {B} p) :',
      f'    ∀ m, Fits raw10Remainder[28]! m → WeightedBound {B} m :=',
      f'  parent_bound_residual {B} (by decide) accepted accepted_good h']
if set(keys)==canon:
    s += ['theorem residual_empty : residual = [] := by decide',
          f'theorem sourceBound : ∀ m, Fits raw10Remainder[28]! m → WeightedBound {B} m :=',
          '  parent_bound (by simp [residual_empty])','#print axioms sourceBound']
s+=['#print axioms parent_bound','end BB6.Agent17.Box28Assembled','']
a.out.write_text('\n'.join(s))
print('accepted',len(keys),'remaining',len(canon)-len(keys),'bound',B)
