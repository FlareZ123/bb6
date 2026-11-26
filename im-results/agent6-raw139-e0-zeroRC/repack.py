"""Repack the four interrupted ZRC roots without changing any proof term.

Recover declaration-level dependencies and remove cross-child batching edges.
Usage: python repack.py WORK (WORK/imports contains original generated modules).
"""
import re, sys, json
from functools import cache
from pathlib import Path
work=Path(sys.argv[1]); out=work/'imports'
roots=(0,7,12,18)
chunk_re=re.compile(r'(?ms)^set_option maxRecDepth 1000000\n.*?^end BB6\.Agent6E0ZeroRC\n')
blockmap={}; allgroups=[]; report={}
for f in sorted(out.glob('ZRCBlock*.lean')):
    for h in re.findall(r'^namespace BB6\.Agent6E0ZeroRCBlocks\.H(\d+)$',f.read_text(),re.M):
        assert h not in blockmap,h
        blockmap[h]=f.stem
for root in roots:
    prefix=f'ZRCRoot{root:02d}'
    old=sorted(out.glob(prefix+'Batch*.lean')); assert old
    declared={}; chunks=[]
    for f in old:
        s=f.read_text(); s=re.sub(r'^import \w+\n','',s,flags=re.M)
        cs=chunk_re.findall(s); assert not chunk_re.sub('',s).strip(),f
        chunks.extend(cs)
    for s in chunks:
        name=re.search(r'^def p('+prefix+r'(?:_\d+)*) :',s,re.M).group(1)
        assert name not in declared
        deps=set(re.findall(r'\.covered p(\w+) c\1\b',s))
        assert deps<=declared.keys(),(name,deps-declared.keys())
        mods={'Hybrid'}|{blockmap[h] for h in re.findall(r'\.proven BB6\.Agent6E0ZeroRCBlocks\.H(\d+)\.ctr',s)}
        if 'BB6.Agent6E0ZeroRCRecurrence.' in s: mods.add('E0ZeroRCRecurrence')
        declared[name]=(s,deps,mods)
    assert prefix in declared and list(declared)[-1]==prefix
    mapping={}; pending=[]; kid=None; weight=0; serial=0; kidtops=[]; new=[]
    def flush():
        global pending,weight,serial
        if not pending:return
        name=f'ZRCRecovery{root:02d}Kid{kid:02d}Batch{serial:04d}';serial+=1
        here=set(pending); deps=set(); ss=[]
        for n in pending:
            s,ds,ms=declared[n];ss.append(s);deps.update(ms);deps.update(mapping[d] for d in ds-here);mapping[n]=name
        (out/(name+'.lean')).write_text(''.join('import '+d+'\n' for d in sorted(deps))+'\n'.join(ss)); new.append(name)
        pending=[];weight=0
    for n,(s,ds,ms) in declared.items():
        if n==prefix:break
        k=int(n.split('_')[1])
        if kid!=k or len(pending)>=12 or weight+len(s)>40000:
            flush();kid=k
        pending.append(n);weight+=len(s)
        if n==f'{prefix}_{k}':
            flush();kidtops.append(mapping[n])
    flush()
    s,ds,ms=declared[prefix]; deps=ms|{mapping[d] for d in ds}
    (out/(prefix+'.lean')).write_text(''.join('import '+d+'\n' for d in sorted(deps))+s)
    for f in old:f.unlink()
    recovered=[]
    for name in new+[prefix]: recovered.extend(chunk_re.findall((out/(name+'.lean')).read_text()))
    assert sorted(recovered)==sorted(chunks)
    allgroups.extend(kidtops); report[prefix]={'old_batches':len(old),'new_batches':len(new),'kids':len(kidtops),'declarations':len(chunks)}
    assert len(kidtops)==len(ds)
assert len(allgroups)==63
@cache
def closure(name):
    f=out/(name+'.lean')
    return {name}|set().union(*(closure(x) for x in re.findall(r'^import (\w+)$',f.read_text(),re.M) if (out/(x+'.lean')).exists()))
@cache
def size(name):return (out/(name+'.lean')).stat().st_size
def total(names):return sum(map(size,names))
groups=[[] for _ in range(16)]; covered=[set() for _ in groups]
for k in sorted(allgroups,key=lambda k:(-total(closure(k)),k)):
    c=closure(k)
    g=min(range(len(groups)),key=lambda i:(total(covered[i]|c),i))
    groups[g].append(k);covered[g].update(c)
(work/'recovery-groups').mkdir(exist_ok=True)
for i,g in enumerate(groups):
    assert g
    (work/'recovery-groups'/f'{i:02d}.txt').write_text(''.join(x+'\n' for x in g))
assert sorted(x for g in groups for x in g)==sorted(allgroups)
print(json.dumps(report,indent=2))
print('Group source bytes:',[total(c) for c in covered],flush=True)
