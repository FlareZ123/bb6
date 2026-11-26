#!/usr/bin/env python3
"""Rebuild exact Raw40 A1=1RC,C1=0LB parent audit (Round21)."""
import os,pathlib,subprocess,sys,json
root=pathlib.Path(__file__).resolve().parent
out=root/'round21'/'shards-input'
out.mkdir(parents=True,exist_ok=True)
p='1RB1RC_1RC---_0RD0LB_1LD1LA_------_------'
for f in ('enumerate_canon','farbank'):
    subprocess.run(['g++','-std=c++20','-O3',str(root/(f+'.cpp')),'-o',str(out/f)],check=True)
subprocess.run([str(out/'enumerate_canon'),p],cwd=out,check=True)
opens=(out/'open.txt').read_text().splitlines()
assert len(opens)==274
with (out/'far5.txt').open('w') as f:
    subprocess.run([str(out/'farbank'),'5'],input=''.join(f'{i} {s.replace("_","")}\n' for i,s in enumerate(opens)),text=True,stdout=f,check=True)
rows=[json.loads(x) for x in (root/'round21-pumps.jsonl').read_text().splitlines()]
assert len(rows)==19
farids={int(x.split()[0]) for x in (out/'far5.txt').read_text().splitlines()}
pumpids={r[0] for r in rows}
assert len(farids)==254 and len(pumpids)==19 and not farids & pumpids
assert farids|pumpids|{236}==set(range(len(opens))) and 236 not in farids|pumpids
for r in rows: assert opens[r[0]].replace('_','')==r[1]
assert opens[236]=='1RB1RC_1RC1RE_0RD0LB_1LD1LA_1LC1RF_---1RB'
(out/'proven.txt').write_text(''.join(f'{opens[r[0]]} BB6.Agent19Raw40.Round21.Leaf{r[0]}\n' for r in rows)+f'{opens[236]} BB6.Agent19Raw40.Leaf236\n')
with (root/'Raw40Round21Pump.lean').open('w') as f:
    subprocess.run([sys.executable,str(root/'emit_autopump.py'),str(root/'round21-pumps.jsonl'),'BB6.Agent19Raw40.Round21'],stdout=f,check=True)
src=(root/'certify_canonical.py').read_text()
anchor="if any('Counter17' in v for v in proven.values()):imports+='import Raw40Counter17\\n'"
assert anchor in src
src=src.replace(anchor,anchor+"\nimports+='import Raw40Round21Pump\\nimport Raw40Leaf236\\n'")
sys.argv=[str(root/'certify_canonical.py'),str(out),str(out/'shards'),p,'101','Raw40C1RC0LB','96']
os.environ['RAW40_STANDALONE']='1'
exec(compile(src,sys.argv[0],'exec'),{'__file__':sys.argv[0],'__name__':'__main__'})
