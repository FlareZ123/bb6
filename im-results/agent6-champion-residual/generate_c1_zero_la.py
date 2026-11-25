#!/usr/bin/env python3
"""Deterministic full four-hole C1=0LA certificate; all witnesses checked by Lean."""
from collections import Counter
from pathlib import Path
import subprocess
import tempfile
import generate_c1_one_lc as base

ROOT = (7,24,11,24,14,0,3,16,12,11,24,24)
HARD = {
 (7,4,11,23,14,0,3,16,12,11,13,24): ('C1ZeroLAFour','.a'),
 (7,6,11,23,14,0,3,16,12,11,24,13): ('C1ZeroLAFour','.b'),
 (7,20,11,24,14,0,3,16,12,11,13,23): ('C1ZeroLAFour','.c'),
 (7,13,11,24,14,0,3,16,12,11,24,24): ('C1ZeroLAFour','.d'),
 (7,21,11,24,14,0,3,16,12,11,3,0): ('C1ZeroLAVars','.v84'),
 (7,21,11,24,14,0,3,16,12,11,3,4): ('C1ZeroLAVars','.v85'),
 (7,21,11,24,14,0,3,16,12,11,3,7): ('C1ZeroLACarry86',''),
 (7,21,11,24,14,0,3,16,12,11,3,8): ('C1ZeroLAVars','.v87'),
 (7,21,11,24,14,0,3,16,12,11,3,10): ('C1ZeroLAVars','.v89'),
 (7,21,11,24,14,0,3,16,12,11,3,11): ('C1ZeroLAVars','.v90'),
 (7,21,11,24,14,0,3,16,12,11,3,16): ('C1ZeroLAVars','.v91'),
 (7,21,11,24,14,0,3,16,12,11,3,18): ('C1ZeroLAVars','.v92'),
 (7,21,11,24,14,0,3,16,12,11,3,19): ('C1ZeroLAVars','.v93'),
 (7,23,11,24,14,0,3,16,12,11,20,13): ('C1ZeroLAVars','.v156'),
 (7,21,11,1,14,0,3,16,12,11,12,24): ('C1ZeroLASweeps.Pair96','false'),
 (7,23,11,1,14,0,3,16,12,11,7,24): ('C1ZeroLASweeps.Pair96','true'),
 (7,21,11,9,14,0,3,16,12,11,15,24): ('C1ZeroLASweeps.GroupD','.v107'),
 (7,21,11,11,14,0,3,16,12,11,15,24): ('C1ZeroLASweeps.GroupD','.v108'),
 (7,21,11,19,14,0,3,16,12,11,15,24): ('C1ZeroLASweeps.GroupD','.v110'),
 (7,23,11,3,14,0,3,16,12,11,5,24): ('C1ZeroLASweeps.Single137',''),
 (7,23,11,9,14,0,3,16,12,11,5,24): ('C1ZeroLASweeps.Single139',''),
 (7,23,11,13,14,0,3,16,12,11,5,24): ('C1ZeroLASweeps.Single140',''),
}
LATE_HOLE = (7,21,11,24,14,0,3,16,12,11,3,9)
LATE_CYCLE = (7,21,11,13,14,0,3,16,12,11,5,24)

def build():
    pending = []
    def walk(p):
        a = base.scan(p,250)
        if a[0] == 'cycle':
            return a
        if a[0] == 'open':
            pending.append(p)
            return a
        _, n, s = a
        if p.count(24) == 1:
            return ('last',n,s)
        return ('split',n,s,[walk(base.refine(p,s,m)) for m in range(24)])
    tree = walk(ROOT)
    with tempfile.TemporaryDirectory() as d:
        exe = Path(d)/'far'
        subprocess.run(['g++','-std=c++17','-O3',str(Path(__file__).with_name('c1_one_lc_far.cpp')),'-o',str(exe)],check=True)
        inp = ''.join(f'{i} '+' '.join(map(str,p))+'\n' for i,p in enumerate(pending))
        raw = subprocess.run([str(exe),'5'],input=inp,text=True,capture_output=True,check=True).stdout
    witness = {pending[a[0]]:a[1:] for line in raw.splitlines() if (a:=list(map(int,line.split())))[1]!=-1}
    assert len(pending)==160 and len(witness)==136,(len(pending),len(witness))
    assert set(pending)-set(witness)==set(HARD)|{LATE_HOLE,LATE_CYCLE}
    assert base.scan(LATE_HOLE,260)==('hole',260,3)
    used = set()
    ct = Counter()
    max_hole = 0
    def fill(p,t):
        nonlocal max_hole
        if t[0]=='open':
            if p in witness: t=('far',witness[p])
            elif p==LATE_HOLE: t=('last',260,3)
            elif p==LATE_CYCLE: t=('cycle',2075,10,True,39)
            else:
                assert p in HARD,p
                used.add(p)
                t=('hard',*HARD[p])
        ct[t[0]]+=1
        if t[0] in ('last','split'):
            max_hole=max(max_hole,t[1])
        if t[0]=='split':
            return (*t[:3],[fill(base.refine(p,t[2],m),c) for m,c in enumerate(t[3])])
        return t
    tree=fill(ROOT,tree)
    assert used==set(HARD)
    assert ct=={'split':85,'cycle':1252,'last':546,'far':136,'hard':22},ct
    assert max_hole==260,max_hole
    print('census',ct,'max_hole',max_hole)
    return tree,max_hole+6

def generate(tree,bound):
    base.ROOT=ROOT
    src=base.generate(tree,bound)
    a=src.index('import C1OneLCSweep')
    b=src.index('set_option maxRecDepth')
    src=src[:a]+('import C1ZeroLAFour\nimport C1ZeroLAVars\nimport C1ZeroLASweeps\nimport C1ZeroLACarry86\n')+src[b:]
    return src.replace('Agent6C1OneLCParent','Agent6C1ZeroLAParent').replace('cover_oneLC','cover_zeroLA')

if __name__=='__main__':
    tree,bound=build()
    dest=Path(__file__).with_name('C1ZeroLAParent.lean')
    dest.write_text(generate(tree,bound))
    print(dest)
