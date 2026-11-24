#!/usr/bin/env python3
"""Generate untrusted checkpoints; Lean independently verifies every transition."""
import sys
from pathlib import Path
n,K,W = map(int,sys.argv[1:])
assert n>=14 and K>0 and W>0
Q=7*2**n-(n+3)
L=2*(n+3*K+10)+6
cs=[1]
s=['import MarginCert','namespace BB6.Agent43CarryCert',
   'set_option maxRecDepth 100000','set_option maxHeartbeats 0',
   'set_option exponentiation.threshold 10000',
   f'private def q : Nat := 7*2^{n}-({n}+3)',
   f'private def l : Nat := requiredMargin {n} {K}',
   'private def layer0 : List Nat := [1]']
j=0
while j<K:
    start=j
    for _ in range(min(W,K-j)):
        assert all(c!=2 and c+L+j<=Q+2 for c in cs)
        cs=[v//2 for c in cs for v in (c,c+Q-j) if v%2==0]
        j+=1
    s.append(f'private def layer{j} : List Nat := [{",".join(map(str,cs))}]')
    s.append(f'private theorem seg{j} : MarginSafe q l {start} layer{start} {j-start} layer{j} :=\n  margin_sound q l {start} layer{start} layer{j} {j-start} (by decide)')
    if start==0:
        s.append(f'private theorem prefix{j} : MarginSafe q l 0 layer0 {j} layer{j} := seg{j}')
    else:
        s.append(f'private theorem prefix{j} : MarginSafe q l 0 layer0 {j} layer{j} := MarginSafe.append prefix{start} seg{j}')
assert not cs
s += [f'theorem margin{n} : MarginSafe (7*2^{n}-({n}+3)) (requiredMargin {n} {K}) 0 [1] {K} [] := prefix{K}',f'#print axioms margin{n}','end BB6.Agent43CarryCert']
Path(f'Margin{n}.lean').write_text('\n'.join(s)+'\n')
