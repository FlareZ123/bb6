#!/usr/bin/env python3
"""Regenerate the two complete Raw56 E1=0RC unary/sparse/FAR certificates."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
NG = ROOT/'im-results/agent47-raw111-cut'
SPECS = {
    '0RD': (182, {109:'BB6Coverage.Agent1Raw56RDM109',117:'BB6Coverage.Agent1Raw56RDM117',44:'BB6.Agent47SparseNGram.Raw56RDSparse44'},
            ['Raw56RDM109','Raw56RDM117','Raw56RDSparse44'],
            ['d630165b9e22deff5b0be0fc5dc57426d7d4113cc0b892433e75e3621e746358','49203cc6ddd65cded3dc9db459a6c379305ccecc2ea9afa3d4672232933067b3','8b991702d392da29779fb6a6c412edf781bc86b34ccb5e7c8f4dc834eef80f1a','52fdc298856bd95e915269c9627a7eacfdfc6cd7aada440df03a7346076b8d47']),
    '1LE': (316, {111:'BB6Coverage.Agent1Raw56LEM111',126:'BB6Coverage.Agent1Raw56LEM126'},
            ['Raw56LEM111','Raw56LEM126'],
            ['745b535ed180dd3bd7eb2fe4f35df746fc0fb0bf67936fab4fd4a37d6eda4eaf','4e0d5f35126d56557078d7ac903e964ef4bd32da64b7c3ebf28326db885a63ef','04a6df00956bc180bc7ce32a86290a5722d7279a22bbbcd484dae9ceccbb5edc','93f8d123054ccd9326e9ed405e4c888e103012d72f5d92fd9cd8eff475315b1f'])
}

def blob(path, expected):
    data = path.read_bytes()
    assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==expected,path

def sha(path, expected):
    assert hashlib.sha256(path.read_bytes()).hexdigest()==expected,path

def main():
    out=Path(sys.argv[1]).resolve(); out.mkdir(parents=True,exist_ok=True)
    cut=ROOT/'im-results/agent7-raw49/cut.cpp'; far=ROOT/'im-results/agent19-raw40-cut/farbank.cpp'; ngram=NG/'ngram_sparse.cpp'
    for path,digest in [(cut,'88d5dfc4994f8bd203fe3f3def5ea90efda86037'),(far,'30cac1862b3b88d7ba596b359a9dc8503163593d'),(ngram,'98be04b8a574cbdd96bf4e38666972c43ee50ef0'),(NG/'emit_sparse.py','1865c763059eb341936be8f25465fbdb70046eef'),(HERE/'emit_rc_rd.py','f6753bf0e6368a66eadb148d5df61d491068e54a')]: blob(path,digest)
    for name,src in [('cut',cut),('farbank',far),('ngram',ngram)]: subprocess.run(['g++','-O3','-std=c++20',str(src),'-o',str(out/name)],check=True)
    sys.path.insert(0,str(NG)); from emit_sparse import emit
    for v,(count,proven,mods,hashes) in SPECS.items():
        parent=f'1RB---_1RC---_0RD{v}_1LD1LE_---0RC_------'; stem=out/v
        subprocess.run([str(out/'cut'),parent,'1000','32','6',str(stem)],check=True)
        tree,opens,f5,f6,bank=[stem.with_suffix(x) for x in ('.json','.open','.far','.far6','.bank')]
        rows=opens.read_text().splitlines(); assert len(rows)==len(set(rows))==count
        def query(indices):return ''.join(f"{i} {rows[i].replace('_','')}\n" for i in indices).encode()
        with f5.open('wb') as f:subprocess.run([str(out/'farbank'),'5'],input=query(range(count)),stdout=f,check=True)
        found={int(s.split()[0]) for s in f5.read_text().splitlines()}
        with f6.open('wb') as f:subprocess.run([str(out/'farbank'),'6'],input=query(i for i in range(count) if i not in found),stdout=f,check=True)
        for path,digest in zip((tree,opens,f5,f6),hashes):sha(path,digest)
        bank.write_bytes(f5.read_bytes()+f6.read_bytes())
        gen=out/(v+'gen');gen.mkdir(exist_ok=True)
        sparse=[]
        if v=='0RD':
            data=subprocess.check_output([str(out/'ngram'),'8'],input=query([44])).decode().split(maxsplit=1)[1]
            name,ns=emit(gen,44,rows[44],data,width=8,module_name='Raw56RDSparse44',expected=(346,19,29))
            sparse=[[name+'Data',['SparseNGram']]]+[[name+f'Row{j:02}',[name+'Data']] for j in range(12)]+[[name,[name+f'Row{j:02}' for j in range(12)]]]
        mod='Raw56RC'+v;ns='BB6.Agent1Raw56.RC'+v
        s=(HERE/'emit_rc_rd.py').read_text()
        patches={"NS = 'BB6.Agent1Raw56.RCRD'":f'NS = {ns!r}',"MOD = 'Raw56RCRD'":f'MOD = {mod!r}',"PARENT = '1RB---_1RC---_0RD1RD_1LD1LE_---0RC_------'":f'PARENT = {parent!r}',"assert len(rows)==len(set(rows))==102 and rows[3]==M3":f'assert len(rows)==len(set(rows))=={count}',"assert set(bank)==set(range(102))-{3}":f'assert set(bank)==set(range({count}))-set({proven!r})',"['Raw40Nores','Raw56RC_RD_M3']":repr(['Raw40Nores',*mods]),"return f'.proven {PROOF}.table {PROOF}.never' if i==3 else far(bank[i],p)":f'proven = {proven!r}\n            return f\'.proven {{proven[i]}}.table {{proven[i]}}.never\' if i in proven else far(bank[i],p)'}
        for a,b in patches.items():assert s.count(a)==1,a;s=s.replace(a,b)
        emitter=out/('emit_'+v+'.py');emitter.write_text(s)
        subprocess.run([sys.executable,str(emitter),str(tree),str(opens),str(bank),str(gen)],check=True)
        manifest=gen/'manifest.json';manifest.write_text(json.dumps(sparse+json.loads(manifest.read_text()),indent=2)+'\n')
if __name__=='__main__':main()
