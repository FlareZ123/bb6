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

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('branch',choices=['1LA','1RE','0LE','1LE'])
    ap.add_argument('--work',type=Path)
    ap.add_argument('--out',type=Path,default=ROOT)
    ap.add_argument('--limit',type=int,default=1200)
    a=ap.parse_args(); branch=a.branch; prefix='Raw39'+branch
    work=(a.work or ROOT/('_build'+branch)).resolve(); out=a.out.resolve()
    work.mkdir(parents=True,exist_ok=True);out.mkdir(parents=True,exist_ok=True)
    data=json.loads(lzma.decompress(base64.b64decode((ROOT/(branch+'-frontier.json.xz.b64')).read_text())))
    assert not data['residual'],'Incomplete discovery frontier'
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
    for i,s,*_ in data['affine']+data['late']:
        assert opens[i].replace('_','')==s
    run('g++','-O3','-std=c++20',source/'bank.cpp','-o',work/'bank')
    bank=json.loads((ROOT/'lb-witnesses.json').read_text())['bank']
    (work/'bank.txt').write_text('\n'.join(bank)+'\n')
    inp=''.join(f'{i} {s.replace("_","")}\n' for i,s in enumerate(opens))
    r=run(work/'bank',work/'bank.txt',input=inp,text=True,capture_output=True)
    far={int(i):code for i,code in map(str.split,r.stdout.splitlines())}
    expected={x[0] for k in ('asym','rungram','blockgram','runblock','affine','late') for x in data[k]}
    assert len(expected)==sum(len(data[k]) for k in ('asym','rungram','blockgram','runblock','affine','late'))
    assert len(far)==data['far_count'] and set(range(len(opens)))-set(far)==expected
    (work/'far.json').write_text(json.dumps(far))
    run('g++','-O3','-std=c++17',ROOT.parent/'agent32-raw59'/'ngram_asym.cpp','-o',work/'ngram')
    inp=''.join(f'{i} {opens[i]} {l} {r}\n' for i,l,r,n in data['asym'])
    ng=run(work/'ngram',input=inp,text=True,capture_output=True)
    assert not ng.stderr,ng.stderr
    ac=[asym_emit(line,opens) for line in ng.stdout.splitlines()]
    assert sorted(meta for _,meta in ac)==sorted(data['asym'])
    special={}
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
    late={table:(n,s) for _,table,n,s in data['late']}
    def close_late(node):
        if node[0]=='open' and node[1].replace('_','') in late:
            return ['last',*late[node[1].replace('_','')]]
        if node[0]=='split':
            return [*node[:3],[close_late(k) for k in node[3]]]
        return node
    index={s:i for i,s in enumerate(opens)}
    tree=Node(close_late(full),'pChild',data['cut'],index);ids=set(tree.leaves())
    assert tree.size==sum(stats.values()) and ids==set(far)|set(special)
    witnesses={}
    for i,c in far.items():
        d,D,L,R,z=masks(parse(opens[i]),int(c[0]),[int(x,36) for x in c[1:]])
        witnesses[i]=f'.far {bs(int(c[0]))} {d} ⟨0,{D},{L},{R},{z}⟩'
    b=Builder(out,branch,data['bound_candidate'],a.limit,witnesses,special);tree.name='all'+branch
    w,r,q=branch
    b.emit(b.base,['Raw39SemanticChunks'],f'''abbrev p39 : PartialMachine :=
  refine (pathEnd root 2 (path.take 3)).1 (3,true) (some ⟨false,true,0⟩)
abbrev pChild : PartialMachine := refine p39 (0,true) (some ⟨{bs(w=="1")},{bs(r=="R")},{ord(q)-65}⟩)
''')
    top=b.build(tree)
    b.emit(prefix+'Complete',[top],'#print axioms all'+branch+'\n')
    leaves=[(name,size) for name,size,deps in b.modules if size>1 or not any(x.startswith(prefix+'Chunk') for x in deps)]
    groups={f'g{i}':[] for i in range(8)};weights=dict.fromkeys(groups,0)
    for name,size in sorted(leaves,key=lambda x:-x[1]):
        g=min(weights,key=weights.get);groups[g].append(name);weights[g]+=size
    manifest={'root':prefix+'Complete','groups':groups,'weights':weights,'modules':b.modules,'stats':dict(b.stats),'normalized_nodes':tree.size,'open_count':len(ids)}
    (out/('shards-'+branch+'semantic.json')).write_text(json.dumps(manifest,indent=2)+'\n')
    print('candidate full tree',data['stats'],'far',len(far),'special',len(special),'chunks',len(b.modules),'weights',weights,'bound',data['bound_candidate'],flush=True)
if __name__=='__main__':main()
