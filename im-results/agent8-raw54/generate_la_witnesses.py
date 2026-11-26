#!/usr/bin/env python3
"""Generate original-source Lean sweep witnesses from the deterministic LA census."""
from pathlib import Path
import hashlib, subprocess, sys, tempfile
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / 'agent8-tnf-raw117'))
from raw112_multisweep import Machine, C, gen
PARENT = '1RB---_1RC---_0RD---_1LD0LE_1LA0LE_------'
SPECS = """2 E - 0011V 010011 1 7 18 26
13 D 0000001 1111V 1 4 37 2 34
79 C 0111V 11 0111 2 13 32 70
89 D 0000V1001 - 0 4 15 2 30
90 D 0000V1001 - 0 6 15 4 38
92 D 0000V1001 - 0 4 15 2 28
103 B 001 1111V 1 8 25 4 66
143 D 01110111 1111V 1 8 69 4 138
157 C - 101011111V 1 6 32 4 82
163 C 0111V 11 0111 2 11 28 60"""
def enumerate_misses(work):
    for src,name in [(ROOT.parent/'agent47-raw112-cut'/'enumerate_fast.cpp','enumerate'),(ROOT.parent/'agent8-tnf-six'/'bank.cpp','bank')]:
        subprocess.run(['g++','-std=c++17','-O3',str(src),'-o',str(work/name)],check=True)
    subprocess.run([str(work/'enumerate'),PARENT],cwd=work,check=True)
    raw=(work/'open.txt').read_bytes()
    assert hashlib.sha256(raw).hexdigest()=='c6ce7be3631b4544b5528fd717af5628a4b885745f16a8170970ffcc049efb4f'
    rows=raw.decode().splitlines()
    found={int(line.split(':')[0]) for line in subprocess.check_output([str(work/'bank'),str(ROOT/'bank.txt'),str(work/'open.txt')],text=True).splitlines()}
    misses=[s for j,s in enumerate(rows) if j not in found]
    assert len(misses)==164
    assert hashlib.sha256(('\n'.join(misses)+'\n').encode()).hexdigest()=='0abdd7b494f234417e9079f683c2066174dcd3649a5e89070baff4686af3220b'
    return misses
def emit_sweeps(misses,root):
    for line in SPECS.splitlines():
        i,q,l,r,p,jump,entry,a,b=line.split()
        i,jump,entry,a,b=map(int,(i,jump,entry,a,b))
        st=C(q,'' if l=='-' else l,'' if r=='-' else r,p)
        tg=C(q,st.l.replace('V',p*jump+'V'),st.r.replace('V',p*jump+'V'),p)
        source,time=gen(i,Machine(misses[i]),st,tg,entry,jump)
        assert time==(a,b)
        (root/f'Raw54LASweep{i}.lean').write_text(source.replace(f'BB6.Agent8Raw112MultiSweep.M{i}',f'BB6.Agent8Raw54.LA.M{i}'))
if __name__=='__main__':
    with tempfile.TemporaryDirectory() as d:
        emit_sweeps(enumerate_misses(Path(d)),ROOT)
