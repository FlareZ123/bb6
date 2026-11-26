#!/usr/bin/env python3
"""Rebuild complete candidate audits for Raw40 A1=1RC, C1=0LD/0RC."""
import os,pathlib,subprocess,sys,json
root=pathlib.Path(__file__).resolve().parent
n=int(sys.argv[1]); c,B,N,F={24:('0LD',411,155,151),25:('0RC',357,1660,1628)}[n]
p=f'1RB1RC_1RC---_0RD{c}_1LD1LA_------_------'
out=root/f'round{n}'/'shards-input';out.mkdir(parents=True,exist_ok=True)
for f in ('enumerate_canon','farbank'):
    subprocess.run(['g++','-std=c++20','-O3',str(root/(f+'.cpp')),'-o',str(out/f)],check=True)
subprocess.run([str(out/'enumerate_canon'),p],cwd=out,check=True)
opens=(out/'open.txt').read_text().splitlines();assert len(opens)==N
with (out/'far5.txt').open('w') as f:
    subprocess.run([str(out/'farbank'),'5'],input=''.join(f'{i} {s.replace("_","")}\n' for i,s in enumerate(opens)),text=True,stdout=f,check=True)
data=root/f'round{n}-pumps.jsonl'; rows=[json.loads(x) for x in data.read_text().splitlines()]
farids={int(x.split()[0]) for x in (out/'far5.txt').read_text().splitlines()};assert len(farids)==F
extra=(root/f'round{n}-far-extra.txt').read_text();(out/'far_extra.txt').write_text(extra)
ids=farids|{int(x.split()[0]) for x in extra.splitlines()};assert len(ids)==F+len(extra.splitlines())
ns=f'BB6.Agent19Raw40.Round{n}';pm=f'Raw40Round{n}Pump';imports=[pm];proven=[]
def add(rows,ns):
    for r in rows:
        i,s=r[:2];assert i not in ids and opens[i].replace('_','')==s
        ids.add(i);proven.append(f'{opens[i]} {ns}.Leaf{i}\n')
add(rows,ns)
with (root/f'{pm}.lean').open('w') as f:
    subprocess.run([sys.executable,str(root/'emit_autopump.py'),str(data),ns],stdout=f,check=True)
if n==25:
    for kind,mod,emitter in [('nested','Raw40NestedLeaves','emit_nested.py'),('pair','Raw40PairLeaves','emit_pair.py'),('affine','Raw40AffineLeaves',None)]:
        data=root/f'{kind}-certs.jsonl';rows=[json.loads(x) for x in data.read_text().splitlines()]
        add(rows,'BB6.Agent19Raw40.'+kind.capitalize()+'Leaves');imports.append(mod)
        if emitter:
            with (root/f'{mod}.lean').open('w') as f:
                subprocess.run([sys.executable,str(root/emitter),str(data)],stdout=f,check=True)
assert ids==set(range(N))
(out/'proven.txt').write_text(''.join(proven))
src=(root/'certify_canonical.py').read_text()
anchor="if any('Counter17' in v for v in proven.values()):imports+='import Raw40Counter17\\n'"
assert anchor in src
src=src.replace(anchor,anchor+'\nimports+='+repr(''.join(f'import {m}\n' for m in imports)))
sys.argv=[str(root/'certify_canonical.py'),str(out),str(out/'shards'),p,str(B),f'Raw40C1RC{c}','96']
os.environ['RAW40_STANDALONE']='1'
exec(compile(src,sys.argv[0],'exec'),{'__file__':sys.argv[0],'__name__':'__main__'})
