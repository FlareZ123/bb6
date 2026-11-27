"""Replay Agent41's saved C1=0RA partition and emit a compositional proof.
Use exactly the recorded block/FAR/late/long recipes.
Every leaf and split is checked by the existing Lean Hybrid checker.
"""
import json
import sys
from pathlib import Path
from collections import Counter

HERE = Path(__file__).resolve().parent
SAVED = HERE.parent / 'agent41-raw139-c1-zeroRA'
sys.path[:0] = [str(HERE.parent / 'agent48-raw139-f1-oneRA'),
                str(HERE.parent / 'agent48-raw139-f1-oneLA')]
from scan import tree, far, scan, ORDER
from blockcert import generate
from package import block_source, bl, slot

NS = 'BB6.Agent14Raw139C1ZeroRA'
BLOCK_NS = NS + 'Blocks'
B = 14876970
LONG = [7,17,11,23,14,1,3,16,12,11,24,3]
P = [7,24,11,24,14,1,3,16,12,11,24,24]

def main(out):
    spec = json.loads((SAVED / 'spec.json').read_text())
    assert spec['parent'] == P and spec['bound'] == B and not spec['open']
    counts = Counter()
    opens = []
    tr = tree(P, counts, opens, spec['limit'], spec['maxd'])
    assert dict(counts) == spec['counts']
    index = {tuple(t): i for i,t in enumerate(opens)}
    params = {i: args for args, ids in spec['block_groups'] for i in ids}
    late = {int(i): args for i,args in spec['late'].items()}
    fars = {int(i): args for i,args in spec['far'].items()}
    assert spec['long']['78']['table'] == LONG == opens[78]
    assert spec['long']['78']['ordinary'] == B-6
    assert len(opens) == len(index) == 210
    assert len(params) == 186 and len(late) == 12 and len(fars) == 11
    assert set(params) | set(late) | set(fars) | {78} == set(range(210))
    for i,(n,s) in late.items():
        assert opens[i].count(24)==1 and scan(opens[i],n)==('hole',n,s)
    for i,args in fars.items():
        assert far(opens[i],*args) is not None
    out.mkdir(parents=True,exist_ok=True)
    modmap = {}
    for k in range(0,len(params),8):
        name = f'A14C1RABlock{k//8:02}'
        src = ('import BlockFAR2\nimport BlockFARBridge\nimport FastThreeHoleAudit\n'
               'set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n')
        for i in sorted(params)[k:k+8]:
            w,cap,mod,runs,flip,phase = params[i]
            c = generate(opens[i],w,cap,mod,runs,flip,phase=phase)
            assert c is not None, (i,params[i])
            s = block_source(i,opens[i],c).replace('BB6.Agent48F1OneRABlocks',BLOCK_NS)
            if flip:
                s = s.replace('theorem same : ctr =','theorem same : BB6Coverage.FAR.reflectPartial ctr =')
                s = s.replace(
                    'BB6BlockFAR.transfer_never machine m (by simpa only [← same] using hm) forever',
                    'BB6Coverage.FAR.reflectNever m (BB6BlockFAR.transfer_never machine _ (by simpa only [← same] using BB6Coverage.FAR.reflectCompatible ctr m hm) forever)')
            src += s
            modmap[i] = name
        (out/(name+'.lean')).write_text(src)
    def size(n):
        return sum(map(size,n[3])) if n[0]=='split' else 1
    assert size(tr)==2002
    def hard(n):
        return any(map(hard,n[3])) if n[0]=='split' else n[0]=='open' and index[tuple(n[1])]==78
    def plain(n,deps):
        k,*a=n
        if k=='split':
            return f'.split {a[0]} {slot(a[1])} (byMove [\n'+',\n'.join(plain(ch,deps) for ch in a[2])+'])'
        if k=='cycle':
            e,t,r,z=a
            return f'.cycle {e} {t} {bl(r)} ({z})'
        if k=='last':
            return f'.last {a[0]} {slot(a[1])}'
        if k=='far':
            rev,d,dfa,t0,t1,z=a
            return f'.far {bl(rev)} {d} ⟨0,{dfa},{t0},{t1},{z}⟩'
        if k=='open':
            i=index[tuple(a[0])]
            if i in late:
                return plain(('last',*late[i]),deps)
            if i in fars:
                return plain(('far',*far(a[0],*fars[i])),deps)
            assert i in params,i
            deps.add(modmap[i])
            pre=f'{BLOCK_NS}.H{i}'
            return f'.proven {pre}.ctr {pre}.never'
        raise ValueError(k)
    common=f'''set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace {NS}
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10FastAudit BB6.Agent6Hybrid
'''
    def emit(n,t,name,force=False):
        deps={'Hybrid'}
        if not force and not hard(n) and size(n)<=120:
            term='.closed ('+plain(n,deps)+')'
        elif n[0]=='open':
            assert index[tuple(n[1])]==78 and t==LONG
            deps.add('LongLeafCover')
            term='.covered BB6.Agent14C1ZeroRALong.p BB6.Agent14C1ZeroRALong.weighted'
        else:
            _,steps,s,children=n
            assert t[s]==24 and len(children)==24
            terms=[]
            for j,(ch,v) in enumerate(zip(children,ORDER)):
                t2=t[:s]+[v]+t[s+1:]
                if force or ch[0]=='split' or hard(ch):
                    cn=f'{name}_{j:02}'
                    emit(ch,t2,cn)
                    deps.add(cn)
                    terms.append(f'.covered p{cn} c{cn}')
                else:
                    terms.append('.closed ('+plain(ch,deps)+')')
            term=f'.split {steps} {slot(s)} (byHybridMove [\n'+',\n'.join(terms)+'])'
        src=''.join(f'import {d}\n' for d in sorted(deps))+common
        src+=f'''def p{name} : PartialMachine := fromCodes {t}
def t{name} : Hybrid {B} := {term}
theorem c{name} : Cover (WeightedBound {B}) p{name} :=
  sound {B} p{name} t{name} (by decide +kernel) (fromCodes_nohalt _) (by decide +kernel)
#print axioms c{name}
'''
        if force:
            src+=f'''def parent : PartialMachine := p{name}
theorem weighted : Cover (WeightedBound {B}) parent := c{name}
#print axioms weighted
'''
        src+=f'end {NS}\n'
        (out/(name+'.lean')).write_text(src)
    emit(tr,P,'A14C1RAParent',True)
    print('Replayed exact recorded partition: 2002 terminal leaves, 210 special recipes; emitted compositional Lean source.')

if __name__=='__main__':
    main(Path(sys.argv[1]))
