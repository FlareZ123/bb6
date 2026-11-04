"""Deterministically generate 106 kernel-checked low valuation Sheep exclusions."""
from functools import lru_cache
from math import gcd
from pathlib import Path
from tempfile import NamedTemporaryFile
from filelock import FileLock
import os
import sys

CONES={402:[(0,0,1,(2,5,7)),(3,-2,15,(8,10)),(9,-4688,1485,(16,18))],
       1738:[(0,0,1,(2,5)),(3,-2,15,(8,)),(6,-196,135,(12,14,16))]}
SURVIVE={(402,0,1,1),(402,1,1,4),(1738,0,1,1),(1738,1,0,2)}

@lru_cache(None)
def order2(m):
    p,v=1,2%m
    while v!=1:
        v=2*v%m
        p+=1
    return p

def generate():
    lines=['import SheepPeriodicGate','set_option maxRecDepth 4096',
           'set_option maxHeartbeats 0','namespace SheepChainLow','']
    count=0
    for r,nodes in CONES.items():
        for ix,(s,b,d,limits) in enumerate(nodes):
            for h,amax in enumerate(limits):
                for a in range(1,amax):
                    D=d*3**h
                    m=D*(2**(a+1)+1)
                    C=2*a*D+2**(h+1)*(d-b)
                    shift=3*D
                    base=r+s+h+1
                    cycle=order2(m)//gcd(order2(m),4860)
                    assert pow(2,4860*cycle,m)==1
                    good=[k for k in range(cycle) if
                          (pow(2,base+4860*k,m)+shift)%m == C%m]
                    keep=(r,ix,h,a) in SURVIVE
                    assert good==(list(range(cycle)) if keep else [])
                    if keep: continue
                    count+=1
                    name=f'r{r}_n{ix}_h{h}_a{a}'
                    lines += [f'theorem {name} (k v : Nat)',
                      f'    (heq : {m}*v+{C} = 2^({base}+4860*k)+{shift}) : False := by',
                      '  exact SheepPeriodicGate.no_generic_equation',
                      f'    {m} {base} {shift} {C} {cycle} k v',
                      '    (by decide) (by decide)',
                      '    (by rw [←Nat.powMod_def]; decide)',
                      '    (by simpa only [Nat.powMod_def, Nat.add_mod, Nat.mod_mod] using',
                      f'      (show ∀ t : Fin {cycle},',
                      f'        (Nat.powMod 2 ({base}+4860*t.val) {m}+{shift})%{m} ≠ {C}%{m} from by decide))',
                      '    heq','']
    assert count==106
    lines += ['#print axioms r402_n0_h0_a1',
              '#print axioms r1738_n2_h2_a15','end SheepChainLow']
    return '\n'.join(lines)+'\n'

if __name__=='__main__':
    path=Path(sys.argv[1] if len(sys.argv)>1 else 'ChainLowCases.lean')
    with FileLock(str(path)+'.lock'):
        with NamedTemporaryFile('w',encoding='utf-8',dir=path.parent,delete=False) as f:
            f.write(generate())
            f.flush()
            os.fsync(f.fileno())
            tmp=f.name
        os.replace(tmp,path)
    print('106 exact all-k Lean certificates generated')
