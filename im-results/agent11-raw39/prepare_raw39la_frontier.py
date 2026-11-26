"""Regenerate the normalized Raw39 0LA frontier and candidate Lean leaves.
This is discovery, not a proof of a complete child Bound.
"""
import argparse, hashlib, json, subprocess
from collections import Counter
from pathlib import Path
from rungram_regen import discover
from prepare_semantic_branch import asym_emit, rungram_emit
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
    ap.add_argument('--work',type=Path,default=ROOT/'_build0LA')
    ap.add_argument('--out',type=Path,default=ROOT)
    a=ap.parse_args(); work=a.work.resolve(); out=a.out.resolve()
    work.mkdir(parents=True,exist_ok=True);out.mkdir(parents=True,exist_ok=True)
    data=json.loads((ROOT/'la-frontier.json').read_text())
    source=ROOT.parent/'agent11-raw121'
    run('g++','-O3','-std=c++17',source/'fast_enum.cpp','-o',work/'enum')
    run(work/'enum',data['child'],cwd=work)
    opens=[];stats=Counter()
    t=project(json.loads((work/'tree.json').read_text()),4,opens,stats)
    assert dict(stats)==data['stats']
    raw=json.dumps(t,separators=(',',':'))+'\n'
    assert sha(raw.encode())==data['normalized_tree_sha256']
    assert sha(('\n'.join(opens)+'\n').encode())==data['open_sha256']
    (work/'normalized-tree.json').write_text(raw)
    (work/'normalized-open.txt').write_text('\n'.join(opens)+'\n')
    for i,s,*_ in data['residual']+data['late']:
        assert opens[i].replace('_','')==s
    run('g++','-O3','-std=c++20',source/'bank.cpp','-o',work/'bank')
    bank=json.loads((ROOT/'lb-witnesses.json').read_text())['bank']
    (work/'bank.txt').write_text('\n'.join(bank)+'\n')
    inp=''.join(f'{i} {s.replace("_","")}\n' for i,s in enumerate(opens))
    r=run(work/'bank',work/'bank.txt',input=inp,text=True,capture_output=True)
    far={int(i):code for i,code in map(str.split,r.stdout.splitlines())}
    expected={x[0] for k in ('asym','rungram','residual','late') for x in data[k]}
    assert len(expected)==sum(len(data[k]) for k in ('asym','rungram','residual','late'))
    assert len(far)==data['far_count'] and set(range(len(opens)))-set(far)==expected
    (work/'far.json').write_text(json.dumps(far))
    run('g++','-O3','-std=c++17',ROOT.parent/'agent32-raw59'/'ngram_asym.cpp','-o',work/'ngram')
    inp=''.join(f'{i} {opens[i]} {l} {r}\n' for i,l,r,n in data['asym'])
    a=run(work/'ngram',input=inp,text=True,capture_output=True)
    assert not a.stderr,a.stderr
    ac=[asym_emit(line,opens) for line in a.stdout.splitlines()]
    assert sorted(meta for _,meta in ac)==sorted(data['asym'])
    groups=[];group=[];size=0
    for code,meta in ac:
        if group and size+meta[3]>2000:groups.append(group);group=[];size=0
        group.append(code);size+=meta[3]
    if group:groups.append(group)
    for j,group in enumerate(groups):
        ns=f'BB6.Agent11Raw39LAAsym{j:02}'
        h=f'import AsymNGram\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace {ns}\nopen BB6Coverage\nopen BB6.Agent1NGram (Trie)\nopen BB6.Agent32AsymNGram\n'
        (out/f'Raw39LAAsym{j:02}.lean').write_text(h+'\n'.join(group)+f'\nend {ns}\n')
    for i,*p,n in data['rungram']:
        dl,dr,states,edges=discover(opens[i],p[:5],p[5:])
        assert states==n,(i,states,n)
        ns=f'BB6.Agent11Raw39LARunGram{i}'
        h=f'import FastBiDFA\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace {ns}\nopen BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1NGram BB6.Agent32FastBiDFA\n'
        (out/f'Raw39LARunGram{i}.lean').write_text(h+rungram_emit(i,opens[i],dl,dr,(states,edges))+f'\nend {ns}\n')
    print('candidate frontier',data['stats'],'far',len(far),'asym',len(ac),'rungram',len(data['rungram']),'late',data['late'],'residual',data['residual'])
if __name__=='__main__':main()
