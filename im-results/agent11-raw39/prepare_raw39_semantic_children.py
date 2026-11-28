"""Regenerate the normalized Raw39 0LA frontier and candidate Lean leaves.
The candidate semantic tree is checked independently by Lean.
"""
import argparse, hashlib, json, subprocess, base64, lzma
from collections import Counter
from pathlib import Path
from rungram_regen import discover, RunDFA
from blockgram_regen import BlockDFA, RunBlockDFA
from minimize_bi import minimize
from prepare_semantic_branch import asym_emit, rungram_emit, Node, Builder, bs
from prepare_raw39 import masks, parse
from gen_rc_counters import m, nextword
from prepare_le_residual import ConditionalBuilder, custom_le
ROOT=Path(__file__).resolve().parent

def run(*args,**kw):
    return subprocess.run([str(x) for x in args],check=True,**kw)

def sha(b):
    return hashlib.sha256(b).hexdigest()

def project(node,cut,opens,stats):
    stats[node[0]]+=1
    if node[0]=='open':opens.append(node[1])
    if node[0]!='split':return node
    assert len(node[3])==24
    return [*node[:3],[project(k,max(cut,i%6+1),opens,stats)
                       for i,k in enumerate(node[3]) if i%6<=cut]]

class MixedBoundBuilder(Builder):
    """Preserve accepted low-bound chunks; lift only potentially costly ancestors."""
    def __init__(self,out,branch,B,limit,far,special,tree,high):
        super().__init__(out,branch,B,limit,far,special)
        self.high=high
        self.raised=set()
        def visit(t):
            needed=t.tag in ('last','split') and t.v[0]+6>B
            for k in t.kids:
                needed=visit(k) or needed
            if needed:self.raised.add(t)
            return needed
        assert visit(tree)
    def bound_leaf(self,t,imports):
        if t not in self.raised:return super().bound_leaf(t,imports)
        low=self.B;self.B=self.high
        try:return super().bound_leaf(t,imports)
        finally:self.B=low
    def compose(self,t):
        if t not in self.raised:return super().compose(t)
        low=self.B;self.B=self.high
        try:code=super().compose(t)
        finally:self.B=low
        names={k.name for k in t.kids if k not in self.raised}
        return '\n'.join(
            f'  · exact BB6.Agent43Raw391LEBoundLift.mono (by decide : {low} ≤ {self.high}) '+line.removeprefix('  · exact ')
            if line.removeprefix('  · exact ') in names else line
            for line in code.splitlines())+'\n'
    def write(self,ts,body,imports,size):
        if any(t in self.raised and not self.small(t) for t in ts):
            imports=imports|{'Raw391LEBoundLift'}
        return super().write(ts,body,imports,size)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('branch',choices=['1LA','1RE','0LE','1LE'])
    ap.add_argument('--work',type=Path)
    ap.add_argument('--out',type=Path,default=ROOT)
    ap.add_argument('--limit',type=int,default=1200)
    ap.add_argument('--conditional',action='store_true',help='emit an explicit residual hypothesis theorem, never a Complete module')
    a=ap.parse_args(); branch=a.branch; prefix='Raw39'+branch
    work=(a.work or ROOT/('_build'+branch)).resolve(); out=a.out.resolve()
    work.mkdir(parents=True,exist_ok=True);out.mkdir(parents=True,exist_ok=True)
    data=json.loads(lzma.decompress(base64.b64decode((ROOT/(branch+'-frontier.json.xz.b64')).read_text())))
    # The frozen 1LE data underestimated its late leaf's incoming blank delay.
    # Agent43Raw391LELate.parent_not_bound proves 28310 impossible.
    if branch=='1LE':
        assert data['bound_candidate']==28310
        data['bound_candidate']=28311
    custom=custom_le(branch,out)
    original_residual=dict(data['residual'])
    assert set(custom)<=set(original_residual)
    residual=set(original_residual)-set(custom)
    assert not residual or a.conditional,'Incomplete discovery frontier: '+str(sorted(residual))
    assert not a.conditional or residual,'Use complete mode when no residual remains'
    cycles=data.get('cycles',[])
    source=ROOT.parent/'agent11-raw121'
    run('g++','-O3','-std=c++17',source/'fast_enum.cpp','-o',work/'enum')
    run(work/'enum',data['child'],cwd=work)
    opens=[];stats=Counter()
    full=json.loads((work/'tree.json').read_text())
    t=project(full,data['cut'],opens,stats)
    assert dict(stats)==data['stats']
    raw=json.dumps(t,separators=(',',':'))+'\n'
    assert sha(raw.encode())==data['normalized_tree_sha256']
    assert sha(('\n'.join(opens)+'\n').encode())==data['open_sha256']
    (work/'normalized-tree.json').write_text(raw)
    (work/'normalized-open.txt').write_text('\n'.join(opens)+'\n')
    for i,s,*_ in data['affine']+data['late']+cycles+data['residual']:
        assert opens[i].replace('_','')==s
    run('g++','-O3','-std=c++20',source/'bank.cpp','-o',work/'bank')
    bank=json.loads((ROOT/'lb-witnesses.json').read_text())['bank']
    (work/'bank.txt').write_text('\n'.join(bank)+'\n')
    inp=''.join(f'{i} {s.replace("_","")}\n' for i,s in enumerate(opens))
    r=run(work/'bank',work/'bank.txt',input=inp,text=True,capture_output=True)
    far={int(i):code for i,code in map(str.split,r.stdout.splitlines())}
    partitions=[data[k] for k in ('asym','rungram','blockgram','runblock','affine','late','residual')]+[cycles]
    expected={x[0] for part in partitions for x in part}
    assert len(expected)==sum(map(len,partitions))
    assert len(far)==data['far_count'] and set(range(len(opens)))-set(far)==expected
    (work/'far.json').write_text(json.dumps(far))
    run('g++','-O3','-std=c++17',ROOT.parent/'agent32-raw59'/'ngram_asym.cpp','-o',work/'ngram')
    inp=''.join(f'{i} {opens[i]} {l} {r}\n' for i,l,r,n in data['asym'])
    ng=run(work/'ngram',input=inp,text=True,capture_output=True)
    assert not ng.stderr,ng.stderr
    ac=[asym_emit(line,opens) for line in ng.stdout.splitlines()]
    assert sorted(meta for _,meta in ac)==sorted(data['asym'])
    special=dict(custom)
    groups=[];group=[];size=0
    for code,meta in ac:
        if group and size+meta[3]>2000:groups.append(group);group=[];size=0
        group.append((code,meta));size+=meta[3]
    if group:groups.append(group)
    for j,group in enumerate(groups):
        ns=f'BB6.Agent11{prefix}Asym{j:02}'
        h=f'import AsymNGram\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace {ns}\nopen BB6Coverage\nopen BB6.Agent1NGram (Trie)\nopen BB6.Agent32AsymNGram\n'
        mod=f'{prefix}Asym{j:02}'
        (out/(mod+'.lean')).write_text(h+'\n'.join(code for code,meta in group)+f'\nend {ns}\n')
        for _,(i,*_) in group:
            name=f'{ns}.M{i}';special[i]=(mod,name+'.table',name+'.never')
    for kind,dfa,width in [('rungram',RunDFA,5),('blockgram',BlockDFA,4),('runblock',RunBlockDFA,5)]:
        for i,*p,n in data[kind]:
            dl,dr,states,edges=discover(opens[i],p[:width],p[width:],dfa=dfa)
            assert states==n,(i,states,n)
            dl,dr,states,edges=minimize(opens[i],[dl,dr])
            ns=f'BB6.Agent11{prefix}DFA{i}'
            h=f'import FastBiDFA\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace {ns}\nopen BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1NGram BB6.Agent32FastBiDFA\n'
            mod=f'{prefix}DFA{i}'
            (out/(mod+'.lean')).write_text(h+rungram_emit(i,opens[i],dl,dr,(states,edges))+f'\nend {ns}\n')
            name=f'{ns}.M{i}';special[i]=(mod,name+'.table',name+'.never')
    for i,table,entry,q,l,r,aa,bb in data['affine']:
        st=m.C(q,tuple(map(tuple,l)),tuple(map(tuple,r)))
        tg=m.C(q,nextword(st.l),nextword(st.r))
        p=m.parse(table)
        ans=m.pump(p,st,tg,3500)
        assert ans is not None,i
        code,cost=m.generate(i,p,(entry,st,tg,ans))
        assert tuple(cost)==(entry,aa,bb),(i,cost)
        mod=f'{prefix}Affine{i}';ns='BB6.Agent11'+mod
        h=f'import SweepPumping\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace {ns}\nopen BB6Coverage BB6Coverage.Agent31Pump\n'
        (out/(mod+'.lean')).write_text(h+code+f'\nend {ns}\n')
        name=f'{ns}.M{i}';special[i]=(mod,name+'.table',name+'.never')
    # The late leaf is a genuine final hole, so the original weighted checker
    # independently checks its trajectory, final hole and delay.
    closed={table:['last',n,s] for _,table,n,s in data['late']}
    closed.update({table:['cycle',e,k,r,b] for _,table,e,k,r,b in cycles})
    assert len(closed)==len(data['late'])+len(cycles)
    def close_late(node):
        if node[0]=='open':return closed.get(node[1].replace('_',''),node)
        if node[0]=='split':return [*node[:3],[close_late(k) for k in node[3]]]
        return node
    index={s:i for i,s in enumerate(opens)}
    tree=Node(close_late(full),'pChild',data['cut'],index);ids=set(tree.leaves())
    assert tree.size==sum(stats.values()) and ids==set(far)|set(special)|residual
    assert len(ids)==len(far)+len(special)+len(residual)
    witnesses={}
    for i,c in far.items():
        d,D,L,R,z=masks(parse(opens[i]),int(c[0]),[int(x,36) for x in c[1:]])
        witnesses[i]=f'.far {bs(int(c[0]))} {d} ⟨0,{D},{L},{R},{z}⟩'
    flavor=branch+'Conditional' if residual else branch
    tree.name='all'+branch+('_if_residual' if residual else '')
    b=(ConditionalBuilder(out,flavor,data['bound_candidate'],a.limit,witnesses,special,tree,residual)
       if residual else Builder(out,flavor,data['bound_candidate'],a.limit,witnesses,special))
    if branch=='1LE' and not residual:
        lift='Raw391LEBoundLift.lean'
        if out!=ROOT:(out/lift).write_bytes((ROOT/lift).read_bytes())
        b=MixedBoundBuilder(out,flavor,28310,a.limit,witnesses,special,tree,data['bound_candidate'])
    w,r,q=branch
    base=f'''abbrev p39 : PartialMachine :=
  refine (pathEnd root 2 (path.take 3)).1 (3,true) (some ⟨false,true,0⟩)
abbrev pChild : PartialMachine := refine p39 (0,true) (some ⟨{bs(w=="1")},{bs(r=="R")},{ord(q)-65}⟩)
'''
    if residual:base+='\n'+b.hypotheses()
    b.emit(b.base,['Raw39SemanticChunks'],base)
    top=b.build(tree)
    root=prefix+('Conditional' if residual else 'Complete')
    b.emit(root,[top],'#print axioms '+tree.name+'\n')
    leaves=[(name,size) for name,size,deps in b.modules if size>1 or not any(x.startswith(b.prefix+'Chunk') for x in deps)]
    # Preserve the original eight-group semantic partition and divide
    # only the two expensive groups not yet accepted. The six accepted
    # groups are combined into one cheap precompiled gold group.
    groups={f'g{i}':[] for i in range(8)};weights=dict.fromkeys(groups,0)
    for name,size in sorted(leaves,key=lambda x:-x[1]):
        g=min(weights,key=weights.get);groups[g].append(name);weights[g]+=size
    if branch=='1LE' and not residual:
        accepted=('g0','g2','g3','g4','g6','g7')
        old=groups
        sizes={name:size for name,size in leaves}
        gold=[name for g in accepted for name in old[g]]
        groups={'gold':gold}
        weights={'gold':sum(sizes[name] for name in gold)}
        for target in ('g1','g5'):
            aa,bb=target+'a',target+'b'
            groups[aa]=[];groups[bb]=[]
            weights[aa]=0;weights[bb]=0
            for name in sorted(old[target],key=lambda x:-sizes[x]):
                dest=aa if weights[aa]<=weights[bb] else bb
                groups[dest].append(name);weights[dest]+=sizes[name]
        assert sorted(name for names in groups.values() for name in names)==sorted(name for name,_ in leaves)
        assert all(groups[name] for name in ('gold','g1a','g1b','g5a','g5b'))
    manifest={'root':root,'bound':data['bound_candidate'],'table':data['child'],'conditional':bool(residual),'residual':[[i,original_residual[i]] for i in sorted(residual)],'groups':groups,'weights':weights,'modules':b.modules,'stats':dict(b.stats),'normalized_nodes':tree.size,'open_count':len(ids)}
    (out/('shards-'+branch+('conditional' if residual else 'semantic')+'.json')).write_text(json.dumps(manifest,indent=2)+'\n')
    print('candidate full tree',data['stats'],'far',len(far),'special',len(special),'chunks',len(b.modules),'weights',weights,'bound',data['bound_candidate'],flush=True)
if __name__=='__main__':main()
