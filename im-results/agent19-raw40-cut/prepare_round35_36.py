#!/usr/bin/env python3
"""Rebuild two exact Raw40 B1=0RC children using existing A10RC sweep proofs."""
import os, pathlib, subprocess, sys
root=pathlib.Path(__file__).resolve().parent
n=int(sys.argv[1])
a,B,N,F={35:('0RD',225,196,195),36:('1RB',219,178,177)}[n]
p=f'1RB{a}_1RC0RC_0RD---_1LD1LA_------_------'
out=root/f'round{n}'/'shards-input'
out.mkdir(parents=True,exist_ok=True)
for f in ('enumerate_canon','farbank'):
    subprocess.run(['g++','-std=c++20','-O3',str(root/(f+'.cpp')),'-o',str(out/f)],check=True)
subprocess.run([str(out/'enumerate_canon'),p],cwd=out,check=True)
opens=(out/'open.txt').read_text().splitlines()
assert len(opens)==N
with (out/'far5.txt').open('w') as f:
    subprocess.run([str(out/'farbank'),'5'],input=''.join(f'{i} {s.replace("_","")}\n' for i,s in enumerate(opens)),text=True,stdout=f,check=True)
ids={int(x.split()[0]) for x in (out/'far5.txt').read_text().splitlines()}
assert len(ids)==F
assert [s for i,s in enumerate(opens) if i not in ids]==[f'1RB{a}_1RC0RC_0RD0LE_1LD1LA_1RB1LF_---1LC']
os.environ['RAW40_PROOF_IMPORTS']='Raw40MoreTwoSided'
subprocess.run([sys.executable,str(root/'certify_modular.py'),str(out),str(out/'shards'),p,str(B),f'Raw40C{a}0RC','96','600'],check=True)
