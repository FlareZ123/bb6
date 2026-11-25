"""Generate and kernel-check the exact 14,876,965-step last-hole witness.
Run from anywhere: python reproduce_trace.py WORKDIR [JOBS]
Requires Lean 4.36.0-rc2 (or a compatible version) on PATH.
"""
import base64, hashlib, lzma, os, shutil, subprocess, sys
from pathlib import Path
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor
from functools import lru_cache

HERE = Path(__file__).resolve().parent
P = [7,17,11,23,14,1,3,16,12,11,24,3]
UNIT = 9
records = []

@lru_cache(None)
def visit(k,q,pos,w):
    size=UNIT<<k
    inp=(k,q,pos,w); calls=[]; count=0
    if k==0:
        while 0<=pos<size:
            c=P[2*q+(w>>pos&1)]
            if c==24: break
            w=(w&~(1<<pos))|(((c>>1)&1)<<pos)
            pos+=1 if c&1 else -1
            q=c>>2; count+=1
    else:
        half=size//2; mask=(1<<half)-1
        while 0<=pos<size:
            side=int(pos>=half); offset=side*half
            a=(w>>offset)&mask
            rid,q,p,b,t=visit(k-1,q,pos-offset,a)
            calls.append((rid,side))
            w=(w&~(mask<<offset))|(b<<offset)
            pos=p+offset; count+=t
            if 0<=p<half: break
    rid=len(records)
    records.append((inp,(q,pos,w,count),calls))
    return rid,q,pos,w,count

def loc(q,p,w): return f'⟨{q},({p}),{w}⟩'

def emit(i):
    (k,q,p,w),(q2,p2,w2,c),children=records[i]; n=UNIT<<k
    d=f'def s{i} : Summary := ⟨{loc(q,p,w)}, {loc(q2,p2,w2)}, {c}⟩\n'
    if not k:
        d+=f'theorem h{i} : Sound table {n} s{i} := leaf_sound _ _ _ (by decide +kernel)\n'
    else:
        uses='['+', '.join(f'({str(bool(side)).lower()},s{j})' for j,side in children)+']'
        pr='.nil'
        for j,side in reversed(children): pr=f'(.cons h{j} {pr})'
        d+=f'theorem h{i} : Sound table {n} s{i} := node_sound table {n//2} s{i} {uses} {pr} (by decide +kernel)\n'
    return d

def unpack(src,dst,sha):
    data=lzma.decompress(base64.b64decode(src.read_bytes()))
    assert hashlib.sha256(data).hexdigest()==sha
    dst.write_bytes(data)

def main():
    work=Path(sys.argv[1]).resolve(); jobs=int(sys.argv[2]) if len(sys.argv)>2 else 2
    work.mkdir(parents=True,exist_ok=True)
    unpack(HERE.parent/'agent13-coverage'/'BB6Coverage.lean.xz.b64',work/'BB6Coverage.lean','fbe453c5c170029885ba328bfdd9262600f918a8ce2371c60ecbb843897fd6bd')
    unpack(HERE/'SegmentTrace.lean.xz.b64',work/'SegmentTrace.lean','cd43360ad0ccb1772e376b078e39e559823a165549bd84cd92ec1e101992ab62')
    root=visit(6,0,288,0)
    assert root[0]==6998 and root[1:3]==(5,340) and root[4]==14876964
    assert len(records)==6999 and sum(len(x[2]) for x in records)==16795
    levels=defaultdict(list)
    for i,v in enumerate(records): levels[v[0][0]].append(i)
    previous=['SegmentTrace']; batches=[]
    for k,ids in sorted(levels.items()):
        names=[]
        for t in range(0,len(ids),200):
            name=f'Seg{k}_{t//200}'; names.append(name)
            src='\n'.join('import '+d for d in previous)+'\nset_option maxRecDepth 4096\nset_option maxHeartbeats 0\nnamespace BB6.Agent41SegmentTrace\n'
            src+=''.join(emit(i) for i in ids[t:t+200])+'end BB6.Agent41SegmentTrace\n'
            (work/(name+'.lean')).write_text(src,encoding='utf-8')
        batches.append(names); previous=names
    shutil.copyfile(HERE/'Result78.lean',work/'Result78.lean')
    env={**os.environ,'LEAN_PATH':str(work)}
    def compile(name):
        subprocess.run(['lean','-j','1','-o',name+'.olean',name+'.lean'],cwd=work,env=env,check=True)
    for name in ['BB6Coverage','SegmentTrace']: compile(name)
    for names in batches:
        with ThreadPoolExecutor(max_workers=jobs) as pool: list(pool.map(compile,names))
    compile('Result78')
if __name__=='__main__': main()
