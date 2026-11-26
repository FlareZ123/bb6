"""Generate the three exceptional M448 block automata using the existing checker."""
from pathlib import Path
from itertools import product
import sys,shutil
root=Path(__file__).resolve().parent
out=Path(sys.argv[1]).resolve()
out.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(root.parent/'agent10-raw108'))
import build_lb as b
b.ROOT=out
base='1RB---_1RC0LB_0RD---_1LD1RE_0RF1LF_1RA0LB'.replace('_','')
for i,mod,runs in [(4,2,5),(10,6,4),(16,3,6)]:
    name=f'Raw124M448Kid{i}'
    move=''.join(list(product('01','LR','ABCDEF'))[i])
    table=base[:3]+move+base[6:]
    b.emit_block(name,'BB6.Agent4.'+name,table,dict(width=3,cap=2,mod=mod,runs=runs,flip=False),active=True)
    for suffix in ('Packed','Proof'):
        shutil.copyfile(b.BLOCK/(name+suffix+'.lean'),out/(name+suffix+'.lean'))
