"""Exact-source candidate audits for Raw54 E1=0RE and E1=0RF.

Frozen census/ledger; every untrusted certificate is checked by Lean.
"""
from pathlib import Path
from collections import Counter, defaultdict
import argparse, hashlib, json, subprocess, sys, tempfile
from generate_rf_witnesses import ROOT, masks, parse
from generate_rf_run_quotients import run_search, edge_count
from generate_ra import slot
from emit_mask import emit_data
from generate_sharded_children import assemble
sys.path.insert(0,str(ROOT.parent/"agent8-tnf-raw117"))
import raw112_multisweep as multi

SPECS = {
    "E1RE": dict(parent="1RB---_1RC---_0RD---_1LD0LE_---0RE_------",bound=4076,
                 stats=Counter(split=21265,cycle=375448,last=101865,open=11783),
                 open_sha="900a840398ab32e0d28bc83993a9b3dc35d7d2a2ac1753346b34adc849b3ceac",
                 miss_sha="1f915928ae8b63032145f20f6459c66b9e27f959fafaafb66359024ecb5e9d7b",
                 hits=11413,misses=370,tags=Counter(F=181,N=68,R=85,S=31,H=2,U=3),
                 hard={240:"E1RE.M240",290:"E1RE.M290",356:"E1RE.M356"}),
    "E1RF": dict(parent="1RB---_1RC---_0RD---_1LD0LE_---0RF_------",bound=840,
                 stats=Counter(split=33292,cycle=600718,last=145065,open=19934),
                 open_sha="c059c8daa06660bbebc73c963239cf8067356e89ba978bc35c9a93cfda4be407",
                 miss_sha="316ed5a98b5d635af42ef67651dd45e5bccaeb9bb151d6c22c64b9ff98cda28e",
                 hits=19558,misses=376,tags=Counter(F=235,N=84,R=38,S=16,U=3),
                 hard={47:"RF47",85:"E1RF.M85",359:"E1RF.M359"})
}

def mask_ngram(work,i,table,k,label):
    """Exact relabeling of the sparse n-gram push/pop graph.
    The existing MaskBiDFA kernel checker independently certifies closure.
    """
    res=subprocess.check_output([str(work/"ngram"),str(k)],input=f"{i} {table}\n",text=True)
    ident,width,n,L,R,S=res.split()
    assert (int(ident),int(width))==(i,k)
    M=1<<k
    st=[(v//(M*M),(v//M)%M,v%M) for v in map(int,S.rstrip(",").split(","))]
    words=[{0},{0}];rawE=[[],[]]
    for _,l,r in st:words[0].add(l);words[1].add(r)
    for d,raw in enumerate((L,R)):
        for x,m in (map(int,a.split(":")) for a in raw.rstrip(",").split(",")):
            for b in (0,1):
                if m&(1<<b):
                    prev=(x>>1)|(b<<(k-1))
                    rawE[d].append((x,x&1,prev))
                    words[d].update((x,prev))
    ids=[{w:i for i,w in enumerate(sorted(ws))} for ws in words]
    D=[[0]*(2*len(ws)) for ws in words]
    E=[defaultdict(set),defaultdict(set)]
    for d in (0,1):
        for x,b,y in rawE[d]:
            a,c=ids[d][x],ids[d][y]
            assert D[d][2*c+b] in (0,a)
            D[d][2*c+b]=a
            E[d][a].add((b,c))
    S={(s,ids[0][l],ids[1][r]) for s,l,r in st}
    assert len(S)==int(n)
    mod=f"Raw54{label}Mask{i}"
    emit_data(ROOT,mod,table,D,E,S)
    print(mod,len(S),len(D[0])//2,len(D[1])//2,edge_count(E),flush=True)
    return mod,"BB6.Agent32AsymNGram."+mod


def collect(work,label,only_sweeps=False):
    spec=SPECS[label];ns0="BB6.Agent8Raw54."+label
    for folder,src,exe in [
        ("agent47-raw112-cut","enumerate_fast.cpp","enumerate"),
        ("agent8-tnf-six","bank.cpp","bank"),
        ("agent47-raw111-cut","ngram_sparse.cpp","ngram")]:
        subprocess.run(["g++","-O3","-std=c++17",str(ROOT.parent/folder/src),"-o",str(work/exe)],check=True)
    subprocess.run([str(work/"enumerate"),spec["parent"]],cwd=work,check=True)
    raw=(work/"open.txt").read_bytes()
    assert hashlib.sha256(raw).hexdigest()==spec["open_sha"]
    rows=raw.decode().splitlines()
    assert len(rows)==len(set(rows))==spec["stats"]["open"]
    found=dict((int(i),c) for i,c in (l.split(":") for l in subprocess.check_output(
        [str(work/"bank"),str(ROOT/"bank.txt"),str(work/"open.txt")],text=True).splitlines()))
    assert len(found)==spec["hits"]
    misses=[row for i,row in enumerate(rows) if i not in found]
    assert len(misses)==spec["misses"]
    assert hashlib.sha256(("\n".join(misses)+"\n").encode()).hexdigest()==spec["miss_sha"]
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
    for line in (ROOT/(label.lower()+"-ledger.txt")).read_text().splitlines():
        if not line or line.startswith("#"):continue
        tag,*v=line.split()
        if only_sweeps and tag!="S":continue
        if tag=="F":
            code,sep,*ids=v
            assert sep==":"
            for i in map(int,ids):far(misses[i],code);tags[tag]+=1
        elif tag in ("N","R"):
            cut=v.index(":")
            params=tuple(map(int,v[:cut]))
            for i in map(int,v[cut+1:]):
                if tag=="N":
                    k,=params
                    mod,ns=mask_ngram(work,i,misses[i],k,label)
                else:
                    D,n,info=run_search(misses[i],params)
                    assert D is not None,(i,n,info)
                    E,S=info
                    mod=f"Raw54{label}Run{i}"
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
            mod=f"Raw54{label}Sweep{i}"
            ns=f"{ns0}.M{i}"
            (ROOT/(mod+".lean")).write_text(source.replace(f"BB6.Agent8Raw112MultiSweep.M{i}",ns))
            proved(i,mod,ns);tags[tag]+=1
        elif tag=="H":
            i,n,s=map(int,v)
            assert parse(misses[i])[s]=="---" and misses[i].count("---")==1
            put(misses[i],f".last {n} {slot(s)}")
            tags[tag]+=1
        elif tag=="U":
            ids=list(map(int,v))
            assert set(ids)==set(spec["hard"])
            for i in ids:
                mod=f"Raw54{label}Hard{i}"
                assert (ROOT/(mod+".lean")).is_file()
                proved(i,mod,"BB6.Agent8Raw54."+spec["hard"][i])
                tags[tag]+=1
        else:raise ValueError(line)
    if only_sweeps:
        assert tags==Counter(S=spec["tags"]["S"]),tags
    else:
        assert tags==spec["tags"],tags
        assert set(certs)==set(rows)
    return json.loads((work/"tree.json").read_text()),certs,deps

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("label",choices=SPECS)
    ap.add_argument("--threshold",type=int,default=200)
    ap.add_argument("--sweeps-only",action="store_true")
    args=ap.parse_args()
    assert args.threshold>0
    label=args.label;spec=SPECS[label];bound=spec["bound"]
    ns="BB6.Agent8Raw54."+label
    with tempfile.TemporaryDirectory() as d:
        tree,certs,deps=collect(Path(d),label,args.sweeps_only)
        if args.sweeps_only:return
        assemble(ROOT,tree,certs,deps,spec["parent"],bound,label,ns,"Raw54"+label+"Base",spec["stats"],args.threshold)
        root=ROOT/("Raw54"+label+"Complete.lean")
        suffix=f"""
namespace {ns}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
theorem exact_threshold (B : Nat) : (∀ m, compatible parent m → WeightedBound B m) ↔ {bound} ≤ B := by
  constructor
  · intro h
    obtain ⟨m,hm,hh,hd⟩ := Attainer.attained
    have hb := h m hm {bound-1} 0 hh hd
    omega
  · intro h m hm k d hk hd
    exact Nat.le_trans (complete_cover m hm k d hk hd) h
#print axioms exact_threshold
end {ns}
"""
        root.write_text(root.read_text()+suffix)
if __name__=="__main__":main()
