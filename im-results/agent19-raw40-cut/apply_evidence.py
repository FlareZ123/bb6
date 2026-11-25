"""Install indexed FAR/pump/counter/late evidence for one candidate.

The certificate generator and Lean independently verify each claimed leaf.
"""
from pathlib import Path
import sys

d=Path(sys.argv[1]); name=sys.argv[2]
opens=(d/'open.txt').read_text().splitlines()
far=[]; proven=[]; late=[]
for evidence in sys.argv[3:]:
    for line in Path(evidence).read_text().splitlines():
        if not line.strip() or line.startswith('#'): continue
        case,i,kind,value=line.split()
        if case!=name: continue
        code=opens[int(i)]
        if kind=='far': far.append(f'{i} {value}')
        elif kind=='pump': proven.append(f'{code} BB6.Agent19Raw40.Auto.Leaf{value}')
        elif kind=='pump2': proven.append(f'{code} BB6.Agent19Raw40.Auto2.Leaf{value}')
        elif kind=='pump3': proven.append(f'{code} BB6.Agent19Raw40.Auto3.Leaf{value}')
        elif kind=='counter': proven.append(f'{code} BB6.Agent19Raw40.Counter{value}')
        elif kind=='proof': proven.append(f'{code} {value}')
        elif kind=='late': late.append(code+' '+value.replace(',',' '))
        else: raise ValueError(kind)
for fname,rows in [('far_extra.txt',far),('proven.txt',proven),('late.txt',late)]:
    (d/fname).write_text(''.join(x+'\n' for x in rows))
