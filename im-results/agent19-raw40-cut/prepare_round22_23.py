#!/usr/bin/env python3
"""Rebuild exact Raw40 A1=1RC,C1=1LC/1LD parent audits."""
import os,pathlib,subprocess,sys,json
root=pathlib.Path(__file__).resolve().parent
n=int(sys.argv[1]); config={22:('1LC',96,763,749),23:('1LD',114,672,655)}
c,B,N,F=config[n]; p=f'1RB1RC_1RC---_0RD{c}_1LD1LA_------_------'
out=root/f'round{n}'/'shards-input';out.mkdir(parents=True,exist_ok=True)
for f in ('enumerate_canon','farbank'):
    subprocess.run(['g++','-std=c++20','-O3',str(root/(f+'.cpp')),'-o',str(out/f)],check=True)
subprocess.run([str(out/'enumerate_canon'),p],cwd=out,check=True)
opens=(out/'open.txt').read_text().splitlines();assert len(opens)==N
with (out/'far5.txt').open('w') as f:
    subprocess.run([str(out/'farbank'),'5'],input=''.join(f'{i} {s.replace("_","")}\n' for i,s in enumerate(opens)),text=True,stdout=f,check=True)
data=root/f'round{n}-pumps.jsonl'; rows=[json.loads(x) for x in data.read_text().splitlines()]
farids={int(x.split()[0]) for x in (out/'far5.txt').read_text().splitlines()};pumpids={r[0] for r in rows}
assert len(farids)==F and len(rows)==len(pumpids)==N-F and not farids & pumpids and farids|pumpids==set(range(N))
for r in rows: assert opens[r[0]].replace('_','')==r[1]
ns=f'BB6.Agent19Raw40.Round{n}';pm=f'Raw40Round{n}Pump'
(out/'proven.txt').write_text(''.join(f'{opens[r[0]]} {ns}.Leaf{r[0]}\n' for r in rows))
with (root/f'{pm}.lean').open('w') as f:
    subprocess.run([sys.executable,str(root/'emit_autopump.py'),str(data),ns],stdout=f,check=True)
src=(root/'certify_canonical.py').read_text()
anchor="if any('Counter17' in v for v in proven.values()):imports+='import Raw40Counter17\\n'"
assert anchor in src
src=src.replace(anchor,anchor+f"\nimports+='import {pm}\\n'")
sys.argv=[str(root/'certify_canonical.py'),str(out),str(out/'shards'),p,str(B),f'Raw40C1RC{c}','96']
os.environ['RAW40_STANDALONE']='1'
exec(compile(src,sys.argv[0],'exec'),{'__file__':sys.argv[0],'__name__':'__main__'})
