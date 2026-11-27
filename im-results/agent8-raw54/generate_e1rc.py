"""Reproduce the E1=0RC six-hole cylinder's complete candidate audit.
Discovery is untrusted; source-level checks prove every leaf and join.
"""
from pathlib import Path
from collections import Counter
import argparse, hashlib, json, subprocess, sys, tempfile
from generate_rf_witnesses import ROOT, masks, parse, fuse_sparse
from generate_rf_run_quotients import run_search, edge_count
from emit_mask import emit_data
from generate_sharded_children import assemble
sys.path.insert(0,str(ROOT.parent/"agent47-raw111-cut"))
from emit_sparse import emit as emit_ngram
sys.path.insert(0,str(ROOT.parent/"agent8-tnf-raw117"))
import raw112_multisweep as multi
PARENT="1RB---_1RC---_0RD---_1LD0LE_---0RC_------"
NS="BB6.Agent8Raw54.E1RC"
BOUND=623
STATS=Counter(split=12182,cycle=215468,last=58266,open=6453)

def collect(work, only_sweeps=False):
    for folder,src,exe in [
        ("agent47-raw112-cut","enumerate_fast.cpp","enumerate"),
        ("agent8-tnf-six","bank.cpp","bank"),
        ("agent47-raw111-cut","ngram_sparse.cpp","ngram")]:
        subprocess.run(["g++","-O3","-std=c++17",str(ROOT.parent/folder/src),"-o",str(work/exe)],check=True)
    subprocess.run([str(work/"enumerate"),PARENT],cwd=work,check=True)
    raw=(work/"open.txt").read_bytes()
    assert hashlib.sha256(raw).hexdigest()=="5b3dc73ba6e5fb6b95602aa176638767f2387dc6749af31583ff0e8cbe3f6d54"
    rows=raw.decode().splitlines()
    assert len(rows)==len(set(rows))==6453
    found=dict((int(i),c) for i,c in (l.split(":") for l in subprocess.check_output(
        [str(work/"bank"),str(ROOT/"bank.txt"),str(work/"open.txt")],text=True).splitlines()))
    assert len(found)==6085
    misses=[row for i,row in enumerate(rows) if i not in found]
    assert len(misses)==368
    assert hashlib.sha256(("\n".join(misses)+"\n").encode()).hexdigest()=="548b816c7b96f2faea82f920eeadf2b7042fea2250b9da89c632f525231313d6"
    certs,deps={},{}
    tags=Counter()
    def put(row,proof,mod=None):
        assert row not in certs,("duplicate",row)
        certs[row]=proof
        if mod:deps[row]=mod
    def proved(i,mod,ns):
        put(misses[i],f".proven ({ns}.table) ({ns}.never)",mod)
    def far(row,code):
        d,D,L,R,z=masks(parse(row),int(code[0]),[int(c,36) for c in code[1:]])
        put(row,f".far {str(code[0]=='1').lower()} {d} ⟨0,{D},{L},{R},{z}⟩")
    if not only_sweeps:
        for i,c in found.items():far(rows[i],c)
    for line in (ROOT/"e1rc-ledger.txt").read_text().splitlines():
        if not line or line.startswith("#"):continue
        tag,*v=line.split()
        if only_sweeps and tag!="S":continue
        if tag=="F":
            code,*ids=v
            for i in map(int,ids):far(misses[i],code);tags[tag]+=1
        elif tag in ("N","R"):
            cut=v.index(":")
            params=tuple(map(int,v[:cut]))
            for i in map(int,v[cut+1:]):
                if tag=="N":
                    k,=params
                    res=subprocess.check_output([str(work/"ngram"),str(k)],input=f"{i} {misses[i]}\n",text=True)
                    ident,data=res.split(maxsplit=1)
                    assert int(ident)==i
                    width,n,L,R,_=data.split()
                    edges=lambda s:sum(int(a.split(":")[1]).bit_count() for a in s.rstrip(",").split(","))
                    mod,ns=emit_ngram(ROOT,i,misses[i],data,width=k,module_name=f"Raw54E1RCSparse{i}",expected=(int(n),edges(L),edges(R)))
                    fuse_sparse(ROOT,mod)
                else:
                    D,n,info=run_search(misses[i],params)
                    assert D is not None,(i,n,info)
                    E,S=info
                    mod=f"Raw54E1RCRun{i}"
                    emit_data(ROOT,mod,misses[i],D,E,S)
                    ns="BB6.Agent32AsymNGram."+mod
                    print(mod,n,len(D[0])//2,len(D[1])//2,edge_count(E),flush=True)
                proved(i,mod,ns);tags[tag]+=1
        elif tag=="S":
            ident,q,l,r,p,jump,entry,a,b=v
            i,jump,entry,a,b=map(int,(ident,jump,entry,a,b))
            l,r=(x if x!="-" else "" for x in (l,r))
            st=multi.C(q,l,r,p)
            tg=multi.C(q,l.replace("V",p*jump+"V"),r.replace("V",p*jump+"V"),p)
            source,time=multi.gen(i,multi.Machine(misses[i]),st,tg,entry,jump)
            assert time==(a,b),(i,time)
            mod=f"Raw54E1RCSweep{i}"
            ns=f"{NS}.M{i}"
            (ROOT/(mod+".lean")).write_text(source.replace(f"BB6.Agent8Raw112MultiSweep.M{i}",ns))
            proved(i,mod,ns);tags[tag]+=1
        elif tag=="Z":
            i,c,e,k,r,b=v
            assert c=="C"
            i,e,k,r,b=map(int,(i,e,k,r,b))
            put(misses[i],f".cycle {e} {k} {str(bool(r)).lower()} ({b})")
            tags[tag]+=1
        else:raise ValueError(line)
    if only_sweeps:
        assert tags==Counter(S=20),tags
    else:
        assert tags==Counter(F=176,N=100,R=67,S=20,Z=5),tags
        assert set(certs)==set(rows)
    return json.loads((work/"tree.json").read_text()),certs,deps

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--threshold",type=int,default=200)
    ap.add_argument("--sweeps-only",action="store_true")
    args=ap.parse_args()
    assert args.threshold>0
    with tempfile.TemporaryDirectory() as d:
        tree,certs,deps=collect(Path(d),args.sweeps_only)
        if args.sweeps_only:return
        assemble(ROOT,tree,certs,deps,PARENT,BOUND,"E1RC",NS,"Raw54E1RCBase",STATS,args.threshold)
        root=ROOT/"Raw54E1RCComplete.lean"
        source=root.read_text()
        suffix=f"""\nnamespace {NS}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
theorem exact_threshold (B : Nat) : (∀ m, compatible parent m → WeightedBound B m) ↔ 623 ≤ B := by
  constructor
  · intro h
    obtain ⟨m,hm,hh,hd⟩ := Attainer.attained
    have hb := h m hm 622 0 hh hd
    omega
  · intro h m hm k d hk hd
    exact Nat.le_trans (complete_cover m hm k d hk hd) h
#print axioms exact_threshold
end {NS}
"""
        root.write_text(source+suffix)
if __name__=="__main__":main()
