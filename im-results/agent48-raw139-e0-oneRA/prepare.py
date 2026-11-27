#!/usr/bin/env python3
"""Materialize the OneRA candidate partition using saved assignments, not search.

From repository root:
  g++ -O3 -std=c++17 im-results/agent48-raw139-e0-0re/replay.cpp -o /tmp/oneRA-replay
  /tmp/oneRA-replay 450 2 7 24 11 24 14 24 24 16 3 11 24 24 > /tmp/oneRA-part.json
  python3 im-results/agent48-raw139-e0-oneRA/prepare.py /tmp/oneRA-part.json /tmp/oneRA
The output spec is a candidate, not a proof. Reflected/width-four BFAR and
packed long traces need the appropriate source-level proof adapters.
"""
import base64, collections, hashlib, json, lzma, pathlib, sys

def compact(x):
    return json.dumps(x,separators=(',',':')).encode()

raw=lzma.decompress(base64.b64decode(pathlib.Path(__file__).with_name('candidate.json.xz.b64').read_text()))
assert hashlib.sha256(raw).hexdigest()=='b31b9a1b4e6f76e1141d7e50add8f5682bd54d083eb74ad62552eb1c28df926d'
s=json.loads(raw)
p=json.loads(pathlib.Path(sys.argv[1]).read_text())
out=pathlib.Path(sys.argv[2]);out.mkdir(parents=True,exist_ok=True)
assert p['counts']==s['counts']
assert hashlib.sha256(compact(p['open'])).hexdigest()==s['open_sha256']
assert len(s['assignment'])==len(p['open'])
index={tuple(t):i for i,t in enumerate(p['open'])}
assert len(index)==len(p['open'])
opens=[];groups=collections.defaultdict(list);late={};proven={};seen=set()

def first_hole(t,n):
    q=h=0;tape=set()
    for k in range(n+1):
        slot=2*q+int(h in tape);v=t[slot]
        if v==24:return k,slot
        if v&2:tape.add(h)
        else:tape.discard(h)
        q=v//4;h+=1 if v&1 else -1
    return None

def emit(t,recipe=None,trace=None,lemma=None):
    i=len(opens);opens.append(t)
    if recipe is not None:groups[tuple(recipe)].append(i)
    elif trace is not None:
        assert t.count(24)==1 and first_hole(t,trace[0])==tuple(trace)
        late[i]=trace
    else:
        assert t==[7,24,11,21,14,9,12,16,3,11,18,23]
        proven[i]=lemma
    return ['open',t]

def graft(node):
    if node[0]=='split':
        return [*node[:3],[graft(n) for n in node[3]]]
    if node[0]!='open':return node
    t=node[1];i=index[tuple(t)];k=str(i);a=s['assignment'][i]
    assert i not in seen;seen.add(i)
    if a==253:return emit(t,lemma=s['proven'][k])
    if a==254:return emit(t,trace=s['late'][k])
    if a!=255:return emit(t,recipe=s['recipes'][a])
    n,slot=s['splits'][k]
    assert t.count(24)==2 and first_hole(t,n)==(n,slot)
    kids=[]
    # replay.cpp / package6.py order: write, direction, next state
    for w in range(2):
        for d in range(2):
            for q in range(6):
                v=4*q+2*w+d;u=t.copy();u[slot]=v
                r=s['children'][k][str(v)]
                kids.append(emit(u,trace=r[1:]) if r[0]=='late' else emit(u,recipe=r))
    return ['split',n,slot,kids]

tree=graft(p['tree'])
assert len(seen)==8223 and len(opens)==8269
assert len({tuple(t) for t in opens})==len(opens)
assert sum(map(len,groups.values()))==8205 and len(late)==63 and len(proven)==1
assert max(n for n,_ in late.values())==529708
counts=dict(p['counts']);counts.update(split=27115,open=8269,maxquery=749)
p.update(tree=tree,open=opens,counts=counts)
spec=dict(parent=s['parent'],counts=counts,limit=450,maxd=2,bound=s['bound'],
    namespace='BB6.Agent48Raw139E0OneRA',prefix='Raw139E0OneRA',
    external_imports=['H4620'],block_groups=[[list(r),groups[r]] for r in sorted(groups)],
    late=late,proven=proven,max_module_leaves=1800,independent_root_children=True)
(out/'partition.json').write_bytes(compact(p)+b'\n')
(out/'spec-compact.json').write_bytes(compact(spec)+b'\n')
print('Candidate graft: 27115 splits; 623646 leaves; 8205 BFAR, 63 late, 1 proven in open leaves; bound 529714 (unaccepted).')
