"""Produce the exact weighted Cover shards from the pinned witness manifest.
Every open branch is checked against its table; only the two explicit exceptional
premises can be assumed. All ordinary certificates are checked by Lean.
"""
import argparse, collections, hashlib, json, pathlib, re, sys
BASE=pathlib.Path(__file__).resolve().parent
ROOT=BASE.parents[1]
sys.path[:0]=[str(ROOT/'im-results/agent48-raw139-f1-oneRA'),str(ROOT/'im-results/agent48-raw139-f1-oneLA')]
from blockcert import generate
from package import block_source, bl, slot
from scan import far
from decode import decode
B=19007
P=[7,24,11,24,14,24,24,16,20,11,24,24]
ORDER=[4*q+2*w+r for w in range(2) for r in range(2) for q in range(6)]
NS='BB6.Agent14E0LFParent'
OPEN={3862:[7,10,11,19,14,17,24,16,20,11,3,0],3863:[7,10,11,21,14,17,24,16,20,11,3,0]}
EXCEPT={i:(f'BB6.Agent14E0LFResidualCycles.p{i}',f'BB6.Agent14E0LFResidualCycles.never{i}') for i in (3864,4344,11287)}
for i in (1307,3002,4125):
    p=f'BB6.Agent3E0LFResidual{i}'; EXCEPT[i]=(p+'.ctr',p+'.never')
for i in (2040,10338):
    p=f'BB6Coverage.Agent14E0LFResidual{i}'; EXCEPT[i]=(p+'.ctr',p+'.never')
p='BB6.Agent14E0LFResidual9015';EXCEPT[9015]=(p+'.ctr',p+'.never')
HEADER='set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nnamespace '+NS+'\nopen BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10FastAudit BB6.Agent14ConditionalHybrid\n'

def load(partition):
    raw=partition.read_bytes()
    assert hashlib.sha256(raw).hexdigest()=='7b5f285a7ce7e323e3d3f6f0c85fe0ba60177d694be3e5d35b87f05b7491052b'
    p=json.loads(raw)
    base,ext,hard=decode(BASE/'recipes.b64')
    idx={tuple(t):i for i,t in enumerate(p['open'])}
    assert len(idx)==len(base)==12646
    children={}
    for i,r in base.items():
        if r[0]=='split':
            children[i]=list(range(12646+24*len(children),12646+24*(len(children)+1)))
    used=set();used_ext=set();used_hard=set();blocks={};exception={}
    def finish(i,t,r):
        if r[0]=='block':
            blocks[i]=(t,r[1]);return ['block',i]
        if r[0] in ('late','hole'):
            assert t.count(24)==1 and t[r[2]]==24
            return ['last',*r[1:]]
        if r[0]=='cycle':return ['cycle',*r[1:]]
        if r[0]=='far':
            w=far(t,r[1],r[2]);assert w is not None,(i,t,r)
            return ['far',*w]
        if r[0]=='split':
            _,n,s=r;assert t[s]==24
            return ['split',n,s,[extended(children[i][v],t[:s]+[v]+t[s+1:]) for v in ORDER]]
        raise ValueError((i,r))
    def extended(i,t):
        assert i not in used_ext;used_ext.add(i)
        r=ext[i]
        if r[0]=='open':
            assert i not in used_hard;used_hard.add(i)
            r=hard[i]
            if r[0]=='open':
                assert t.count(24)==1 and i in EXCEPT.keys()|OPEN.keys()
                if i in OPEN:assert t==OPEN[i]
                exception[i]=t
                return ['exception',i]
        return finish(i,t,r)
    def expand(n,t):
        if n[0]=='split':
            _,k,s,kids=n;assert t[s]==24 and len(kids)==24
            return ['split',k,s,[expand(kids[v],t[:s]+[v]+t[s+1:]) for v in ORDER]]
        if n[0]!='open':return n
        assert n[1]==t
        i=idx[tuple(t)];assert i not in used;used.add(i)
        r=base[i]
        return extended(i,t) if r[0]=='open' else finish(i,t,r)
    tree=expand(p['tree'],P)
    assert used==base.keys() and used_ext==ext.keys() and used_hard==hard.keys()
    assert len(blocks)==12371 and set(exception)==EXCEPT.keys()|OPEN.keys()
    counts=collections.Counter()
    def tally(n):
        counts[n[0]]+=1
        if n[0]=='split':
            for ch in n[3]:tally(ch)
    tally(tree);assert counts['split']==27892 and sum(counts.values())-counts['split']==641517
    print('expanded exact witness tree:',dict(counts),flush=True)
    return tree,blocks

def make(partition,out,roots,cap=185,packed=False,split_root13=False):
    tree,blocks=load(partition);out.mkdir(parents=True,exist_ok=True)
    modmap={};manifest=[]
    def put(name,s,deps):
        (out/(name+'.lean')).write_text(''.join('import '+x+'\n' for x in sorted(set(deps)))+s)
        manifest.append(name)
    def bids(n):
        if n[0]=='split':return [i for ch in n[3] for i in bids(ch)]
        return [n[1]] if n[0]=='block' else []
    def pack(ids,k):
        for start in range(0,len(ids),8):
            name=f'ZLFBlock{k:02d}_{start//8:04d}';s='set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n'
            for i in ids[start:start+8]:
                t,(w,c,m,z,f,ph)=blocks[i]
                data=generate(t,w,c,m,z,bool(f),event_limit=150000,phase=bool(ph));assert data is not None,(i,t)
                src=block_source(i,t,data).replace('BB6.Agent48F1OneRABlocks','BB6.Agent14E0LFBlocks')
                if f:
                    src=src.replace('theorem same : ctr =','theorem same : BB6Coverage.FAR.reflectPartial ctr =')
                    src=src.replace('BB6BlockFAR.transfer_never machine m (by simpa only [← same] using hm) forever','BB6Coverage.FAR.reflectNever m (BB6BlockFAR.transfer_never machine _ (by simpa only [← same] using BB6Coverage.FAR.reflectCompatible ctr m hm) forever)')
                s+=src;modmap[i]=name
            put(name,s,{'BlockFAR2','BlockFARBridge','FastThreeHoleAudit','FARBi'})
    def unresolved(n):return any(map(unresolved,n[3])) if n[0]=='split' else n[0]=='exception' and n[1] in OPEN and (not packed or n[1]!=3863)
    def size(n):return sum(map(size,n[3])) if n[0]=='split' else 1
    def leaf(n,deps):
        k,*a=n
        if k=='cycle':e,s,r,x=a;return f'.cycle {e} {s} {bl(r)} ({x})'
        if k=='last':return f'.last {a[0]} {slot(a[1])}'
        if k=='far':
            rev,d,dfa,t0,t1,z=a;return f'.far {bl(rev)} {d} ⟨0,{dfa},{t0},{t1},{z}⟩'
        if k=='block':
            i=a[0];deps.add(modmap[i]);p=f'BB6.Agent14E0LFBlocks.H{i}';return f'.proven {p}.ctr {p}.never'
        if k=='exception':
            i=a[0]
            if i==3863 and packed:
                deps.add('E0LF3863Packed');return '.proven BB6.Agent14E0LF3863.ctr BB6.Agent14E0LF3863.never'
            p,h=EXCEPT[i];deps.add('E0LFPortfolio');return f'.proven {p} {h}'
        raise ValueError(n)
    def plain(n,deps):
        if n[0]!='split':return leaf(n,deps)
        return f'.split {n[1]} {slot(n[2])} (byMove [\n'+',\n'.join(plain(ch,deps) for ch in n[3])+'])'
    def emit(n,t,name,prem):
        deps={'ConditionalHybrid'}
        if prem!='True':deps.add('ZLFOpen')
        if not unresolved(n) and size(n)<=cap:term=f'.closed ({plain(n,deps)})'
        elif n[0]=='exception':
            i=n[1];assert t==OPEN[i] and prem=='premise'
            proof='fun h => h' if packed else ('fun h => h.1' if i==3862 else 'fun h => h.2')
            term=f'.covered (fromCodes {t}) ({proof})'
        else:
            _,k,s,kids=n;terms=[]
            for j,(ch,v) in enumerate(zip(kids,ORDER)):
                t2=t[:s]+[v]+t[s+1:]
                if ch[0]=='split' or unresolved(ch) or (split_root13 and name=='ZLFRoot13'):
                    cn=f'{name}_{j}';emit(ch,t2,cn,prem);deps.add(cn);terms.append(f'.covered p{cn} c{cn}')
                else:terms.append(f'.closed ({plain(ch,deps)})')
            term=f'.split {k} {slot(s)} (byHybridMove [\n'+',\n'.join(terms)+'])'
        src=HEADER+f'def p{name} : PartialMachine := fromCodes {t}\ndef t{name} : Hybrid {B} {prem} := {term}\ntheorem c{name} : {prem} → Cover (WeightedBound {B}) p{name} :=\n  sound {B} p{name} t{name} (by decide +kernel) (fromCodes_nohalt _) (by decide +kernel)\n#print axioms c{name}\nend {NS}\n'
        put(name,src,deps)
    prem=f'Cover (WeightedBound {B}) (fromCodes {OPEN[3862]})'
    if not packed:prem+=f' ∧ Cover (WeightedBound {B}) (fromCodes {OPEN[3863]})'
    (out/'ZLFOpen.lean').write_text('import ConditionalHybrid\n'+HEADER+f'def premise : Prop := {prem}\nend {NS}\n')
    _,k,s,kids=tree;assert (k,s)==(8,10)
    for root in roots:
        n=kids[root];t=P[:s]+[ORDER[root]]+P[s+1:]
        pack(bids(n),root)
        assert unresolved(n)==(root==18)
        emit(n,t,f'ZLFRoot{root:02d}','premise' if root==18 else 'True')
    batch(out,manifest,split_root13=split_root13)
    print('generated',len(manifest),'pre-batch modules',flush=True)

def batch(out,names,split_root13=False):
    groups={};result=[];pending=[];weight=0;idx=0
    def flush():
        nonlocal pending,weight,idx
        if not pending:return
        name=f'{"ZLF13" if split_root13 else pending[0][0].split("_")[0]}Batch{idx:04d}';idx+=1
        deps=set();sources=[];here={n for n,s,d in pending}
        for n,s,d in pending:
            deps|={groups.get(x,x) for x in d if x not in here};sources.append(s);groups[n]=name
        (out/(name+'.lean')).write_text(''.join('import '+x+'\n' for x in sorted(deps))+'\n'.join(sources))
        result.append(name);pending=[];weight=0
    for n in names:
        s=(out/(n+'.lean')).read_text()
        if n.startswith('ZLFBlock'):
            flush();groups[n]=n;result.append(n);continue
        deps=set(re.findall(r'^import (\w+)$',s,re.M));s=re.sub(r'^import \w+\n','',s,flags=re.M)
        if len(pending)>=12 or weight+len(s)>40000:flush()
        pending.append((n,s,deps));weight+=len(s)
        if re.fullmatch(r'ZLFRoot\d\d',n) or (split_root13 and re.fullmatch(r'ZLFRoot13_\d+',n)):flush()
    flush()
    for n in names:
        if n not in result:(out/(n+'.lean')).unlink()
    for n in names:
        if re.fullmatch(r'ZLFRoot\d\d',n) or (split_root13 and re.fullmatch(r'ZLFRoot13_\d+',n)):
            (out/(n+'.lean')).write_text('import '+groups[n]+'\n');result.append(n)
    (out/'batched.txt').write_text('\n'.join(result)+'\n')

def final(out):
    out.mkdir(parents=True,exist_ok=True)
    src='import ZLFOpen\n'+''.join(f'import ZLFRoot{i:02d}\n' for i in range(24))+HEADER
    terms=[f'.covered pZLFRoot{i:02d} '+(f'cZLFRoot{i:02d}' if i==18 else f'(fun _ => cZLFRoot{i:02d} True.intro)') for i in range(24)]
    src+=f'def parent : PartialMachine := fromCodes {P}\ndef root : Hybrid {B} premise := .split 8 (5,false) (byHybridMove [\n'+',\n'.join(terms)+f'])\ntheorem weighted_conditional : premise → Cover (WeightedBound {B}) parent :=\n  sound {B} parent root (by decide +kernel) (fromCodes_nohalt _) (by decide +kernel)\n#print axioms weighted_conditional\nend {NS}\n'
    (out/'E0ZeroLFCover.lean').write_text(src)

if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('out',type=pathlib.Path)
    a.add_argument('--partition',type=pathlib.Path,default=BASE/'partition.json')
    a.add_argument('--roots',type=int,nargs='+',default=list(range(24)))
    a.add_argument('--cap',type=int,default=185);a.add_argument('--packed',action='store_true');a.add_argument('--final',action='store_true');a.add_argument('--split-root13',action='store_true',help='emit independently compilable children of root13')
    a=a.parse_args()
    if a.final:final(a.out)
    else:make(a.partition,a.out,a.roots,a.cap,a.packed,split_root13=a.split_root13)
