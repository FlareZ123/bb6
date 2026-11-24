"""Generate exact untrusted checkpoint literals; Lean checks each segment."""
import sys
from pathlib import Path

n,K,W=map(int,sys.argv[1:])
if n<14 or K<1 or W<1:
    raise ValueError("expected n>=14 and positive K,W")
Q=7*2**n-(n+3)
cs=[1]
s=['import CarryCert','namespace BB6.Agent43CarryCert',
   'set_option maxRecDepth 100000','set_option maxHeartbeats 0',
   'set_option exponentiation.threshold 10000',
   f'private def q : Nat := 7*2^{n}-({n}+3)',
   'private def layer0 : List Nat := [1]']
j=0
while j<K:
    start=j
    for _ in range(min(W,K-j)):
        assert 2 not in cs, (n,j)
        cs=[v//2 for c in cs for v in (c,c+Q-j) if v%2==0]
        j+=1
    s.append(f'private def layer{j} : List Nat := [{",".join(map(str,cs))}]')
    s.append(f'private theorem seg{j} : Safe q {start} layer{start} {j-start} layer{j} :=\n  check_sound q {start} layer{start} layer{j} {j-start} (by decide)')
    if start==0:
        s.append(f'private theorem prefix{j} : Safe q 0 layer0 {j} layer{j} := seg{j}')
    else:
        s.append(f'private theorem prefix{j} : Safe q 0 layer0 {j} layer{j} := Safe.append prefix{start} seg{j}')
assert not cs, (n,K)
s += [f'theorem safe{n} : Safe (7*2^{n}-({n}+3)) 0 [1] {K} [] := prefix{K}',
      f'#print axioms safe{n}','end BB6.Agent43CarryCert']
Path(f'Carry{n}.lean').write_text('\n'.join(s)+'\n',encoding='utf-8')
