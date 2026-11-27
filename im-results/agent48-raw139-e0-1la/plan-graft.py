"""Balance the generated first-hole child proof modules, without searching machines."""
import functools,json,pathlib,sys
w=pathlib.Path(sys.argv[1]); d=w/'imports'; prefix='Raw139E0OneLA'
root=d/(prefix+'Cover.lean')
def deps(p):
    return [m for l in p.read_text().splitlines() if l.startswith('import ') for m in l.split()[1:]]
allfiles={p.stem:p for p in d.glob('*.lean')}
roots=[m for m in deps(root) if m in allfiles]
assert 0<len(roots) and len(roots)==len(set(roots))
@functools.cache
def closure(m):
    if m not in allfiles:return frozenset()
    seen={m}
    for q in deps(allfiles[m]):seen|=closure(q)
    return frozenset(seen)
closures={m:closure(m) for m in roots}
assert set().union(*closures.values())==set(allfiles)-{root.stem}
groups=[[] for _ in range(min(12,len(roots)))]
weights=[0]*len(groups)
size={m:sum(allfiles[q].stat().st_size for q in closures[m]) for m in roots}
for m in sorted(roots,key=lambda m:size[m],reverse=True):
    i=min(range(len(groups)),key=lambda i:weights[i]); groups[i].append(m); weights[i]+=size[m]
assert all(groups)
(w/'shard-plan.json').write_text(json.dumps(groups)+'\n')
print('Root child modules:',len(roots),'shards:',len(groups),'source byte weights:',weights)
