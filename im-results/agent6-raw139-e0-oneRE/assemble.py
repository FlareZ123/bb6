"""Generate checked, compositional branch certificates from reproduce.py output.
The search records are untrusted: every certificate is independently checked by Lean.
"""
import argparse, json, pathlib, re, sys
ROOT=pathlib.Path(__file__).resolve().parents[2]
sys.path[:0]=[str(ROOT/'im-results/agent48-raw139-f1-oneRA'),str(ROOT/'im-results/agent48-raw139-f1-oneLA')]
from blockcert import generate
from package import block_source as original_block_source, bl, slot
B=19745
P=[7,24,11,24,14,24,24,16,19,11,24,24]
ORDER=[4*q+2*w+r for w in range(2) for r in range(2) for q in range(6)]
NS='BB6.Agent6E0OneRE'

def block_source(i,t,data,flip):
    src=original_block_source(i,t,data).replace('BB6.Agent48F1OneRABlocks','BB6.Agent6E0OneREBlocks')
    if data['width']==4:
        src=src.replace('BB6BlockFAR.','BB6BlockFAR4.')
    if flip:
        ns='BB6BlockFAR4' if data['width']==4 else 'BB6BlockFAR'
        src=src.replace('theorem same : ctr =','theorem same : BB6Coverage.FAR.reflectPartial ctr =')
        src=src.replace(f'{ns}.transfer_never machine m (by simpa only [← same] using hm) forever', f'BB6Coverage.FAR.reflectNever m ({ns}.transfer_never machine _ (by simpa only [← same] using BB6Coverage.FAR.reflectCompatible ctr m hm) forever)')
    return src

def load(directory):
    p=json.loads((directory/'partition.json').read_text())
    recipe=dict(map(json.loads,(directory/'recipes.jsonl').read_text().splitlines()))
    children={tuple(i):r for i,r in map(json.loads,(directory/'children.jsonl').read_text().splitlines())}
    return p,recipe,children

def make(p,recipe,children,out,roots,cap=185):
    out.mkdir(parents=True,exist_ok=True)
    idx={tuple(t):i for i,t in enumerate(p['open'])}
    assert len(idx)==len(recipe)==2758
    block={}
    def expand(n,t):
        if n[0]=='split':
            _,k,s,kids=n
            assert len(kids)==24 and t[s]==24
            return ['split',k,s,[expand(ch,t[:s]+[v]+t[s+1:]) for ch,v in zip(kids,ORDER)]]
        if n[0]!='open':return n
        i=idx[tuple(n[1])];r=recipe[i]
        assert t==n[1]
        if i==1873:
            assert t==[7,21,11,17,14,3,2,16,19,11,24,12] and r==['hard']
            return ['hard']
        if i in (479,897,1763,2014):
            assert r[0]=='late' and t.count(24)==1
            return ['longquery',i]
        if r[0]=='late' and t.count(24)>1:
            _,k,s=r
            return ['split',k,s,[finish(children[i,v],100000+i*24+v,t[:s]+[v]+t[s+1:]) for v in ORDER]]
        return finish(r,i,t)
    def finish(r,i,t):
        if r[0]=='block':
            block[i]=(t,r);return ['block',i]
        if r[0]=='late':
            assert t.count(24)==1
            return ['last',*r[1:]]
        assert r[0]=='cycle',r
        return r
    tree=expand(p['tree'],P)
    def size(n):return sum(map(size,n[3])) if n[0]=='split' else 1
    assert size(tree)==357651
    def count_blocks(n):
        if n[0]=='split':return [i for ch in n[3] for i in count_blocks(ch)]
        return [n[1]] if n[0]=='block' else []
    modmap={};manifest=[]
    def put(name,source,deps):
        (out/(name+'.lean')).write_text(''.join('import '+x+'\n' for x in sorted(set(deps)))+source)
        manifest.append(name)
    def pack_blocks(ids,k):
        for start in range(0,len(ids),8):
            name=f'OREBlock{k:02d}_{start//8:04d}'
            s='set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n'
            deps={'BlockFAR2','BlockFARBridge','FastThreeHoleAudit'}
            for i in ids[start:start+8]:
                t,r=block[i];_,w,c,m,z,f,ph,*_=r
                data=generate(t,w,c,m,z,f,event_limit=150000,phase=ph)
                assert data is not None,(i,r)
                if w==4:deps.add('BlockFARBridge4')
                s+=block_source(i,t,data,f);modmap[i]=name
            put(name,s,deps)
    def leaf(n,imports):
        k,*a=n
        if k=='cycle':
            e,s,r,x=a;return f'.cycle {e} {s} {bl(r)} ({x})'
        if k=='last':return f'.last {a[0]} {slot(a[1])}'
        if k=='far':
            rev,d,dfa,t0,t1,z=a;return f'.far {bl(rev)} {d} ⟨0,{dfa},{t0},{t1},{z}⟩'
        if k=='block':
            i=a[0];imports.add(modmap[i]);prefix=f'BB6.Agent6E0OneREBlocks.H{i}'
            return f'.proven {prefix}.ctr {prefix}.never'
        raise ValueError(n)
    def plain(n,imports):
        if n[0]!='split':return leaf(n,imports)
        return f'.split {n[1]} {slot(n[2])} (byMove [\n'+',\n'.join(plain(ch,imports) for ch in n[3])+'])'
    def hard(n):return any(map(hard,n[3])) if n[0]=='split' else n[0] in ('hard','longquery')
    base='set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nnamespace '+NS+'\nopen BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10FastAudit BB6.Agent6Hybrid\n'
    def emit(n,t,name):
        deps={'Hybrid'}
        if not hard(n) and size(n)<=cap:
            term=f'.closed ({plain(n,deps)})'
        elif n[0]=='hard':
            deps.add('OneRE1873');term='.closed (.proven BB6.Agent6E0OneRE1873.p BB6.Agent6E0OneRE1873.never)'
        elif n[0]=='longquery':
            deps.add('OneRELongQueries');i=n[1];term=f'.covered BB6.Agent6E0OneRELongQueries.p{i} BB6.Agent6E0OneRELongQueries.c{i}'
        else:
            _,k,s,kids=n;terms=[]
            for j,(ch,v) in enumerate(zip(kids,ORDER)):
                t2=t[:s]+[v]+t[s+1:]
                if ch[0] in ('split','hard','longquery'):
                    cn=f'{name}_{j}'
                    emit(ch,t2,cn);deps.add(cn);terms.append(f'.covered p{cn} c{cn}')
                else:terms.append(f'.closed ({plain(ch,deps)})')
            term=f'.split {k} {slot(s)} (byHybridMove [\n'+',\n'.join(terms)+'])'
        src=base+f'def p{name} : PartialMachine := fromCodes {t}\ndef t{name} : Hybrid {B} := {term}\ntheorem c{name} : Cover (WeightedBound {B}) p{name} :=\n  sound {B} p{name} t{name} (by decide +kernel) (fromCodes_nohalt _) (by decide +kernel)\n#print axioms c{name}\nend {NS}\n'
        put(name,src,deps)
    _,k,s,kids=tree
    for root in roots:
        n=kids[root];t=P[:s]+[ORDER[root]]+P[s+1:]
        pack_blocks(count_blocks(n),root)
        emit(n,t,f'ORERoot{root:02d}')
    (out/'manifest.txt').write_text('\n'.join(manifest)+'\n')
    batch(out,manifest)
    print('emitted',len(manifest),'modules before batching',flush=True)

def batch(out,names):
    groups={};result=[];pending=[];weight=0;idx=0
    def flush():
        nonlocal pending,weight,idx
        if not pending:return
        name=f'{pending[0][0].split("_")[0]}Batch{idx:04d}';idx+=1
        deps=set();sources=[];here={n for n,s,d in pending}
        for n,s,d in pending:
            deps|={groups.get(x,x) for x in d if x not in here}
            sources.append(s);groups[n]=name
        (out/(name+'.lean')).write_text(''.join('import '+x+'\n' for x in sorted(deps))+'\n'.join(sources))
        result.append(name);pending=[];weight=0
    for n in names:
        s=(out/(n+'.lean')).read_text()
        if n.startswith('OREBlock'):
            flush();groups[n]=n;result.append(n);continue
        deps=set(re.findall(r'^import (\w+)$',s,re.M));s=re.sub(r'^import \w+\n','',s,flags=re.M)
        if len(pending)>=12 or weight+len(s)>40000:flush()
        pending.append((n,s,deps));weight+=len(s)
        if re.fullmatch(r'ORERoot\d\d',n):flush()
    flush()
    for n in names:
        if n not in result:(out/(n+'.lean')).unlink()
    for n in names:
        if re.fullmatch(r'ORERoot\d\d',n):
            (out/(n+'.lean')).write_text('import '+groups[n]+'\n')
            result.append(n)
    (out/'batched.txt').write_text('\n'.join(result)+'\n')

def final(out):
    out.mkdir(parents=True,exist_ok=True)
    src='import Hybrid\n'+''.join(f'import ORERoot{i:02d}\n' for i in range(24))
    src+=f'''set_option maxHeartbeats 0
namespace {NS}
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10FastAudit BB6.Agent6Hybrid
def parent : PartialMachine := fromCodes {P}
def root : Hybrid {B} := .split 10 (2,true) (byHybridMove [
'''+',\n'.join(f'.covered pORERoot{i:02d} cORERoot{i:02d}' for i in range(24))+f'''])
theorem weighted : Cover (WeightedBound {B}) parent :=
  sound {B} parent root (by decide +kernel) (fromCodes_nohalt _) (by decide +kernel)
#print axioms weighted
end {NS}
'''
    (out/'E0OneRECover.lean').write_text(src)

if __name__=='__main__':
    a=argparse.ArgumentParser()
    a.add_argument('out',type=pathlib.Path)
    a.add_argument('--roots',type=int,nargs='+',default=list(range(24)))
    a.add_argument('--cap',type=int,default=185)
    a.add_argument('--directory',type=pathlib.Path,default=pathlib.Path(__file__).resolve().parent)
    a.add_argument('--final',action='store_true')
    a=a.parse_args()
    if a.final:final(a.out)
    else:make(*load(a.directory),a.out,a.roots,a.cap)
