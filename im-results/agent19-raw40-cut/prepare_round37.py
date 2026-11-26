#!/usr/bin/env python3
"""Rebuild Raw40 A1=0RD B1=0RE, including all five saved FAR6 leaves."""
import os, pathlib, subprocess, sys
root=pathlib.Path(__file__).resolve().parent
p='1RB0RD_1RC0RE_0RD---_1LD1LA_------_------'
out=root/'round37'/'shards-input'
out.mkdir(parents=True,exist_ok=True)
for f in ('enumerate_canon','farbank'):
    subprocess.run(['g++','-std=c++20','-O3',str(root/(f+'.cpp')),'-o',str(out/f)],check=True)
subprocess.run([str(out/'enumerate_canon'),p],cwd=out,check=True)
opens=(out/'open.txt').read_text().splitlines()
assert len(opens)==836
with (out/'far5.txt').open('w') as f:
    subprocess.run([str(out/'farbank'),'5'],input=''.join(f'{i} {s.replace("_","")}\n' for i,s in enumerate(opens)),text=True,stdout=f,check=True)
ids={int(x.split()[0]) for x in (out/'far5.txt').read_text().splitlines()}
extra={0:'0012344514401',108:'1012134332533',515:'1010234335151',608:'1012134332533',611:'1012131454434'}
assert len(ids)==831 and set(range(len(opens)))-ids==set(extra)
(out/'far_extra.txt').write_text(''.join(f'{i} {v}\n' for i,v in extra.items()))
os.environ['RAW40_STANDALONE']='1'
subprocess.run([sys.executable,str(root/'certify_canonical.py'),str(out),str(out/'shards'),p,'214','Raw40C0RD0RE','96'],check=True)
