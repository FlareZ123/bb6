#!/usr/bin/env python3
"""Repartition E1=1RC source shard 10; reuse the other 31 accepted shards."""
import argparse, os, re, shutil
from pathlib import Path
from functools import lru_cache
STEM='Raw54E1OneRC'
OLD_COUNT=32
REPAIR_COUNT=12

def plan(generated:Path,out:Path,count:int=REPAIR_COUNT):
    files={p.stem:p for p in generated.glob(STEM+'*.lean')}
    graph={m:[d for d in re.findall(r'^import (\S+)$',p.read_text(),re.M) if d in files]
           for m,p in files.items()}
    weight={m:int((p.stat().st_size+8000)**1.15) for m,p in files.items()}
    @lru_cache(None)
    def closure(m):
        assert m in files,m
        return frozenset([m]).union(*(closure(d) for d in graph[m]))
    def cost(members):return sum(weight[m] for m in members)
    roots=[Path(s).stem for s in (generated/'plan/10.txt').read_text().splitlines()]
    assert len(roots)==len(set(roots))==8,roots
    target=max(1,cost(set().union(*(closure(r) for r in roots)))//count)
    frontier=set()
    def cut(m):
        children=[d for d in graph[m] if d.startswith(STEM+'Shard')]
        if children and cost(closure(m))>target:
            for d in children:cut(d)
        else:frontier.add(m)
    for m in roots:cut(m)
    bins=[[] for _ in range(count)]
    dependencies=[set() for _ in range(count)]
    for root in sorted(frontier,key=lambda m:(-cost(closure(m)),m)):
        i=min(range(count),key=lambda i:(cost(dependencies[i]|closure(root)),i))
        bins[i].append(root);dependencies[i].update(closure(root))
    assert all(bins),[len(b) for b in bins]
    out.mkdir(parents=True,exist_ok=False)
    for i,entries in enumerate(bins):
        (out/f'{i}.txt').write_text(''.join(f'{m}.lean\n' for m in sorted(entries)))
        print(f'bin={i} roots={len(entries)} modules={len(dependencies[i])} '
              f'weight={cost(dependencies[i])} bytes='
              f'{sum(files[m].stat().st_size for m in dependencies[i])}',flush=True)
    print('frontier=',len(frontier),'target=',target,flush=True)

def normalize(old:Path,repair:Path,out:Path,count:int=REPAIR_COUNT):
    out.mkdir(parents=True,exist_ok=False)
    i=0
    for j in range(OLD_COUNT):
        if j==10:continue
        src=old/f'raw54-sliced-slice-{j}'
        assert (src/'manifest.json').is_file(),src
        shutil.copytree(src,out/f'raw54-sliced-slice-{i}',copy_function=os.link)
        i+=1
    for j in range(count):
        src=repair/f'raw54-e1rc-repair10-{j}'
        assert (src/'manifest.json').is_file(),src
        shutil.copytree(src,out/f'raw54-sliced-slice-{i}',copy_function=os.link)
        i+=1
    assert i==OLD_COUNT-1+count
    print('normalized',i,'source-checked slices',flush=True)

if __name__=='__main__':
    a=argparse.ArgumentParser()
    a.add_argument('mode',choices=['plan','normalize'])
    a.add_argument('first',type=Path)
    a.add_argument('second',type=Path)
    a.add_argument('third',nargs='?',type=Path)
    a.add_argument('--count',type=int,default=REPAIR_COUNT)
    p=a.parse_args()
    if p.mode=='plan':
        assert p.third is None
        plan(p.first,p.second,p.count)
    else:
        assert p.third is not None
        normalize(p.first,p.second,p.third,p.count)
