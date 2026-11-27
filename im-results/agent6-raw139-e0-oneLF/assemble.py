"""Generate checked, compositional branch certificates from reproduce.py output.
The search records are untrusted: every certificate is independently checked by Lean.
"""
import argparse, json, pathlib, re, sys
ROOT=pathlib.Path(__file__).resolve().parents[2]
sys.path[:0]=[str(ROOT/'im-results/agent48-raw139-f1-oneRA'),str(ROOT/'im-results/agent48-raw139-f1-oneLA')]
from blockcert import generate
from package import block_source as original_block_source, bl, slot
from ngram_source import emit_ngram
B=90794
P=[7,24,11,24,14,24,24,16,22,11,24,24]
ORDER=[4*q+2*w+r for w in range(2) for r in range(2) for q in range(6)]
NS='BB6.Agent6E0OneLF'

def block_source(i,t,data,flip):
    src=original_block_source(i,t,data).replace('BB6.Agent48F1OneRABlocks','BB6.Agent6E0OneLFBlocks')
    if data['width']==4:
        src=src.replace('BB6BlockFAR.','BB6BlockFAR4.')
    if flip:
        ns='BB6BlockFAR4' if data['width']==4 else 'BB6BlockFAR'
        src=src.replace('theorem same : ctr =','theorem same : BB6Coverage.FAR.reflectPartial ctr =')
        src=src.replace(f'{ns}.transfer_never machine m (by simpa only [← same] using hm) forever', f'BB6Coverage.FAR.reflectNever m ({ns}.transfer_never machine _ (by simpa only [← same] using BB6Coverage.FAR.reflectCompatible ctr m hm) forever)')
    return src

def load(directory):
    p=json.loads((directory/'partition.json').read_text())
    recipe={}
    for f in sorted((directory/'discovery').rglob('recipes.jsonl')):
        for i,r in map(json.loads,f.read_text().splitlines()):
            assert i not in recipe,i
            recipe[i]=r
    assert set(recipe)==set(range(len(p['open'])))
    return p,recipe

def make(p,recipe,out,roots,cap=100):
    out.mkdir(parents=True,exist_ok=True)
    idx={tuple(t):i for i,t in enumerate(p['open'])}
    assert len(idx)==len(recipe)==18046
    records=json.loads(pathlib.Path(__file__).with_name('holdouts.json').read_text())['unresolved']
    exceptional={(r['id'],tuple(map(tuple,r['path']))):r for r in records}
    used=set()
    block={};ngrams={}
    def expand(n,t):
        if n[0]=='split':
            _,k,s,kids=n
            assert len(kids)==24 and t[s]==24
            return ['split',k,s,[expand(ch,t[:s]+[v]+t[s+1:]) for ch,v in zip(kids,ORDER)]]
        if n[0]!='open':return n
        i=idx[tuple(n[1])]
        assert t==n[1]
        return finish(recipe[i],i,t,())
    def finish(r,i,t,path):
        if r[0]=='split':
            _,k,s,kids=r
            assert t[s]==24 and len(kids)==24
            return ['split',k,s,[finish(ch,i,t[:s]+[v]+t[s+1:],path+((s,v),)) for v,ch in zip(ORDER,kids)]]
        if r[0]=='open':
            key=(i,path);rec=exceptional[key]
            assert rec['table']==t==r[1] and key not in used
            used.add(key)
            return ['longcert','H'+str(i)+'_'+str(path[0][1]) if path else 'H'+str(i)]
        if r[0]=='block':
            j=len(block);block[j]=(t,r);return ['block',j]
        if r[0]=='ngram':
            j=len(ngrams);ngrams[j]=(t,r);return ['ngram',j]
        if r[0]=='last':assert t.count(24)==1
        assert r[0] in ('cycle','last','far'),r
        return r
    tree=expand(p['tree'],P)
    assert used==set(exceptional)
    def size(n):return sum(map(size,n[3])) if n[0]=='split' else 1
    assert size(tree)==23*(p['counts']['split']+12)+1==945048
    for j,(t,r) in ngrams.items():emit_ngram(out,j,t,r)
    def count_blocks(n):
        if n[0]=='split':return [i for ch in n[3] for i in count_blocks(ch)]
        return [n[1]] if n[0]=='block' else []
    modmap={};manifest=[]
    def put(name,source,deps):
        (out/(name+'.lean')).write_text(''.join('import '+x+'\n' for x in sorted(set(deps)))+source)
        manifest.append(name)
    def pack_blocks(ids,k):
        for start in range(0,len(ids),8):
            name=f'OLFBlock{k:02d}_{start//8:04d}'
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
        if k=='ngram':
            i=a[0];imports.add(f'OLFNGram{i}');prefix=f'BB6.Agent6OneLFNGram.H{i}'
            return f'.proven {prefix}.p {prefix}.never'
        if k=='block':
            i=a[0];imports.add(modmap[i]);prefix=f'BB6.Agent6E0OneLFBlocks.H{i}'
            return f'.proven {prefix}.ctr {prefix}.never'
        raise ValueError(n)
    def plain(n,imports):
        if n[0]!='split':return leaf(n,imports)
        return f'.split {n[1]} {slot(n[2])} (byMove [\n'+',\n'.join(plain(ch,imports) for ch in n[3])+'])'
    def hard(n):return any(map(hard,n[3])) if n[0]=='split' else n[0]=='longcert'
    base='set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nnamespace '+NS+'\nopen BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent6OneLFZipHybrid\n'
    def emit(n,t,name):
        deps={'OneLFZipHybrid'}
        if n[0]=='longcert':
            deps.add('OneLFExceptionalAudit');pre='BB6.Agent6OneLFExceptional';term=f'.covered {pre}.p{n[1]} {pre}.c{n[1]}'
        elif not hard(n) and size(n)<=cap:
            term=f'.closed ({plain(n,deps)})'
        else:
            _,k,s,kids=n;terms=[]
            for j,(ch,v) in enumerate(zip(kids,ORDER)):
                t2=t[:s]+[v]+t[s+1:]
                if ch[0] in ('split','longcert'):
                    cn=f'{name}_{j}'
                    emit(ch,t2,cn);deps.add(cn);terms.append(f'.covered p{cn} c{cn}')
                else:terms.append(f'.closed ({plain(ch,deps)})')
            term=f'.split {k} {slot(s)} (byHybridMove [\n'+',\n'.join(terms)+'])'
        src=base+f'def p{name} : PartialMachine := fromCodes {t}\ndef t{name} : Hybrid {B} := {term}\ntheorem c{name} : Cover (WeightedBound {B}) p{name} :=\n  sound {B} p{name} t{name} (by decide +kernel) (fromCodes_nohalt _) (by decide +kernel)\n#print axioms c{name}\nend {NS}\n'
        put(name,src,deps)
    _,k,s,kids=tree
    assert (k,s)==(8,10)
    for root in roots:
        n=kids[root];t=P[:s]+[ORDER[root]]+P[s+1:]
        pack_blocks(count_blocks(n),root)
        emit(n,t,f'OLFRoot{root:02d}')
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
        if n.startswith('OLFBlock'):
            flush();groups[n]=n;result.append(n);continue
        deps=set(re.findall(r'^import (\w+)$',s,re.M));s=re.sub(r'^import \w+\n','',s,flags=re.M)
        if pending and pending[0][0].split('_')[:2]!=n.split('_')[:2]:flush()
        if len(pending)>=4 or weight+len(s)>20000:flush()
        pending.append((n,s,deps));weight+=len(s)
        if re.fullmatch(r'OLFRoot\d\d',n):flush()
    flush()
    for n in names:
        if n not in result:(out/(n+'.lean')).unlink()
    for n in names:
        if re.fullmatch(r'OLFRoot\d\d',n):
            (out/(n+'.lean')).write_text('import '+groups[n]+'\n')
            result.append(n)
    (out/'batched.txt').write_text('\n'.join(result)+'\n')

def final(out):
    out.mkdir(parents=True,exist_ok=True)
    src='import OneLFZipHybrid\n'+''.join(f'import OLFRoot{i:02d}\n' for i in range(24))
    src+=f'''set_option maxHeartbeats 0
namespace {NS}
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent6OneLFZipHybrid
def parent : PartialMachine := fromCodes {P}
def root : Hybrid {B} := .split 8 (5,false) (byHybridMove [
'''+',\n'.join(f'.covered pOLFRoot{i:02d} cOLFRoot{i:02d}' for i in range(24))+f'''])
theorem weighted : Cover (WeightedBound {B}) parent :=
  sound {B} parent root (by decide +kernel) (fromCodes_nohalt _) (by decide +kernel)
#print axioms weighted
end {NS}
'''
    (out/'E0OneLFCover.lean').write_text(src)

if __name__=='__main__':
    a=argparse.ArgumentParser()
    a.add_argument('out',type=pathlib.Path)
    a.add_argument('--roots',type=int,nargs='+',default=list(range(24)))
    a.add_argument('--cap',type=int,default=100)
    a.add_argument('--directory',type=pathlib.Path,default=pathlib.Path(__file__).resolve().parent)
    a.add_argument('--final',action='store_true')
    a=a.parse_args()
    if a.final:final(a.out)
    else:make(*load(a.directory),a.out,a.roots,a.cap)
