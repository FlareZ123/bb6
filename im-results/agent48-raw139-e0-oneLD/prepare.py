#!/usr/bin/env python3
"""Graft the immutable OneLD witness manifest; no witness search."""
import base64, collections, hashlib, json, lzma, pathlib, sys

def compact(x):
    return json.dumps(x,separators=(',',':')).encode()

raw=lzma.decompress(base64.b64decode(pathlib.Path(__file__).with_name('candidate.json.xz.b64').read_text()))
assert hashlib.sha256(raw).hexdigest()=='d7d793eba8a5db770ff07806cad6420a7b2bf2720c61a39174225b6fbd28d91e'
s=json.loads(raw)
a=base64.b64decode(s['assignment'])
p=json.loads(pathlib.Path(sys.argv[1]).read_text())
out=pathlib.Path(sys.argv[2]);out.mkdir(parents=True,exist_ok=True)
assert p['counts']==s['counts']
assert hashlib.sha256(compact(p['open'])).hexdigest()==s['open_sha256']
assert len(a)==len(p['open'])==17589
index={tuple(t):i for i,t in enumerate(p['open'])}
assert len(index)==len(p['open'])
opens=[];groups=collections.defaultdict(list);late={};proven={};weighted={};seen=set()

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
        assert lemma['table']==t and t.count(24)==1
        proven[i]=lemma['namespace']
        if lemma['kind']=='weighted':
            assert lemma['bound']==s['bound']
            weighted[i]=lemma
        else:assert lemma['kind']=='never'
    return ['open',t]

def graft(node):
    if node[0]=='split':
        return [*node[:3],[graft(n) for n in node[3]]]
    if node[0]!='open':return node
    t=node[1];i=index[tuple(t)];k=str(i);v=a[i]
    assert i not in seen;seen.add(i)
    if v==252:
        assert i==1784 and t==s['unresolved'][k]==[7,24,11,13,14,23,20,16,14,11,5,1]
        return emit(t,lemma={'table':t,'namespace':'BB6Coverage.Agent48.H1784','kind':'never'})
    if v==253:
        assert i==328 and t==[7,24,11,21,14,5,0,16,14,11,17,5]
        return emit(t,lemma=s['proven'][k])
    if v==254:return emit(t,trace=s['late'][k])
    if v!=255:return emit(t,recipe=s['recipes'][v])
    n,slot=s['splits'][k]
    assert i==9504 and t.count(24)==2 and first_hole(t,n)==(n,slot)
    kids=[]
    for w in range(2):
        for d in range(2):
            for q in range(6):
                mv=4*q+2*w+d;u=t.copy();u[slot]=mv
                r=s['children'][k][str(mv)]
                kids.append(emit(u,trace=r[1:]) if r[0]=='late' else emit(u,recipe=r))
    return ['split',n,slot,kids]

tree=graft(p['tree'])
assert len(seen)==17589 and len(opens)==17612
assert len({tuple(t) for t in opens})==len(opens)
assert sum(map(len,groups.values()))==17501 and len(late)==109 and len(proven)==2 and len(weighted)==1
assert max(n for n,_ in late.values())==85579
counts=dict(p['counts']);counts.update(split=19814,open=17612,maxquery=717)
p.update(tree=tree,open=opens,counts=counts)
spec=dict(parent=s['parent'],counts=counts,limit=450,maxd=2,bound=s['bound'],
    namespace='BB6.Agent48Raw139E0OneLD',prefix='Raw139E0OneLD',
    external_imports=['H1784','H328'],external_module_by_namespace={'BB6Coverage.Agent48.H1784':'H1784','BB6Coverage.Agent48.H328':'H328'},
    block_groups=[[list(r),groups[r]] for r in sorted(groups)],
    late=late,proven=proven,weighted_external=weighted,max_module_leaves=1800,independent_root_children=True)
(out/'partition.json').write_bytes(compact(p)+b'\n')
(out/'spec-compact.json').write_bytes(compact(spec)+b'\n')
print('OneLD exact graft: 19814 splits; 455723 leaves; 17501 BFAR, 109 late, 2 proved-leaf candidates; bound 29607414 (parent unaccepted).')
