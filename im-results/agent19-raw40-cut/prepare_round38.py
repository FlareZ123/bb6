#!/usr/bin/env python3
"""Regenerate the complete Raw40 A1=0RD B1=0LE canonical proof (round 38)."""
import json, os, pathlib, subprocess, sys
root=pathlib.Path(__file__).resolve().parent
p='1RB0RD_1RC0LE_0RD---_1LD1LA_------_------'
out=root/'round38'/'shards-input'
out.mkdir(parents=True,exist_ok=True)
for f in ('enumerate_canon','farbank'):
    subprocess.run(['g++','-std=c++20','-O3',str(root/(f+'.cpp')),'-o',str(out/f)],check=True)
subprocess.run([str(out/'enumerate_canon'),p],cwd=out,check=True)
opens=(out/'open.txt').read_text().splitlines()
assert len(opens)==531
with (out/'far5.txt').open('w') as f:
    subprocess.run([str(out/'farbank'),'5'],input=''.join(f'{i} {s.replace("_","")}\n' for i,s in enumerate(opens)),text=True,stdout=f,check=True)
ids={int(x.split()[0]) for x in (out/'far5.txt').read_text().splitlines()}
assert len(ids)==514
extra={54:'1012133454422',55:'1012133454422',56:'1012133454422',261:'0012322415101',31:'1012322451222',59:'1012322451222',87:'0012322452201',215:'1012322452322',216:'1012322452322',57:'0012344255355'}
rows=[json.loads(x) for x in (root/'round38-pumps.jsonl').read_text().splitlines()]
pumpids={r[0] for r in rows}
assert len(pumpids)==5 and not (ids & (set(extra)|pumpids|{61,357}))
assert set(range(len(opens)))==ids|set(extra)|pumpids|{61,357}
(out/'far_extra.txt').write_text(''.join(f'{i} {v}\n' for i,v in extra.items()))
for r in rows:assert opens[r[0]].replace('_','')==r[1]
assert opens[357]=='1RB0RD_1RC0LE_0RD0RC_1LD1LA_---1LF_1LB0RF'
assert opens[61]=='1RB0RD_1RC0LE_0RD1RB_1LD1LA_---0LF_1LB0RB'
ns='BB6.Agent19Raw40.Round38Pump'
(out/'proven.txt').write_text(''.join(f'{opens[i]} {ns}.Leaf{i}\n' for i in sorted(pumpids))+f'{opens[357]} BB6.Agent19Raw40.Round38Nested\n')
(out/'late.txt').write_text(f'{opens[61]} 1131 8\n')
with (root/'Raw40Round38Pump.lean').open('w') as f:
    subprocess.run([sys.executable,str(root/'emit_autopump.py'),str(root/'round38-pumps.jsonl'),ns],stdout=f,check=True)
os.environ['RAW40_PROOF_IMPORTS']='Raw40Round38Pump Raw40Round38Nested'
subprocess.run([sys.executable,str(root/'certify_modular.py'),str(out),str(out/'shards'),p,'1132','Raw40C0RD0LE','96','600'],check=True)
