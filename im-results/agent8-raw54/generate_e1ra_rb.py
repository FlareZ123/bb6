"""Exact-source sharded audits of Raw54 E1=0RA, 0RB and 1RC cylinders."""
from pathlib import Path
from collections import Counter
import argparse, hashlib, json, subprocess, tempfile
from generate_e1re_rf import ROOT, masks, parse, mask_ngram, multi
from generate_rf_run_quotients import run_search, edge_count
from grouped_run_search import group_search
from generate_late import generate as late, rowdata, maxdelay
from generate_ra import slot
from emit_mask import emit_data
from generate_sharded_children import assemble

SPECS={
 "E1OneRE":dict(parent="1RB---_1RC---_0RD---_1LD0LE_---1RE_------",bound=8212,
    stats=Counter(split=27228,cycle=465210,last=136749,open=24286),
    open_sha="a10f58ce1a267b66303ddbb964e3504bebbedb5c18513a7474d1e1ce0edc7b4f",
    miss_sha="cc1d98e76b3841f24f746d2d4eeb54bb3ce62a2930c7ef0a73a8f0ed94654b75",
    hits=23811,misses=475,tags=Counter(F=207,N=131,R=108,G=24,S=1,H=4),
    attainer=198,n=8211,delay=0),
 "E1OneRC":dict(parent="1RB---_1RC---_0RD---_1LD0LE_---1RC_------",bound=1847,
    stats=Counter(split=18718,cycle=327830,last=91992,open=10693),
    open_sha="ef1e7ed33b01d008f8a8edd3630d762de45ecbc4c87add7ad3f962c4c13eed42",
    miss_sha="c54a699944fb2ca9c8f7dfc399c960923bfacb0f10d24a06e2314e1ec56ce24a",
    hits=10284,misses=409,tags=Counter(F=141,N=150,R=85,G=27,S=3,H=2,U=1),
    attainer=29,n=1846,delay=0),
 "E1RA":dict(parent="1RB---_1RC---_0RD---_1LD0LE_---0RA_------",bound=27669,
    stats=Counter(split=28565,cycle=503924,last=139138,open=13934),
    open_sha="339bef5621fb9a1cc2a900dd30680e3adac2cc1ad7bc21007db77c395983508a",
    miss_sha="3a2e7cad73a90d8cf34cec12b381383a04232374fddf4539f5d7925ffd3020b6",
    hits=13361,misses=573,tags=Counter(F=245,N=162,R=129,G=23,S=6,P=3,H=4,Z=1),
    attainer=502,n=27668,delay=0),
 "E1RB":dict(parent="1RB---_1RC---_0RD---_1LD0LE_---0RB_------",bound=12634,
    stats=Counter(split=34061,cycle=610985,last=156949,open=15470),
    open_sha="67813f52adc4cfecf158b876b578e4e964af865ce7a36b8a4f4fb24f014ce045",
    miss_sha="737cd2d6481e75565cee1301e952609b5e2a7c7ec3da26cc552adec4cf4ffe40",
    hits=14713,misses=757,tags=Counter(F=276,N=221,R=210,G=35,S=4,H=9,Z=2),
    attainer=301,n=12632,delay=1)
}

def collect(work,label):
    spec=SPECS[label]
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
    certs,deps,leaf_checks={},{},{}
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
    for i,c in found.items():far(rows[i],c)
    for line in (ROOT/(label.lower()+"-ledger.txt")).read_text().splitlines():
        if not line or line.startswith("#"):continue
        tag,*v=line.split()
        if tag=="F":
            code,sep,*ids=v
            assert sep==":"
            for i in map(int,ids):far(misses[i],code);tags[tag]+=1
        elif tag in ("N","R","G"):
            cut=v.index(":")
            params=tuple(map(int,v[:cut]))
            for i in map(int,v[cut+1:]):
                if tag=="N":
                    k,=params
                    mod,ns=mask_ngram(work,i,misses[i],k,label)
                else:
                    search=run_search if tag=="R" else group_search
                    D,n,info=search(misses[i],params)
                    assert D is not None,(i,n,info)
                    E,S=info
                    mod=f"Raw54{label}{'Run' if tag=='R' else 'Group'}{i}"
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
            ns=f"BB6.Agent8Raw54.{label}.M{i}"
            (ROOT/(mod+".lean")).write_text(source.replace(f"BB6.Agent8Raw112MultiSweep.M{i}",ns))
            proved(i,mod,ns);tags[tag]+=1
        elif tag=="P":
            mod,sep,*ids=v
            assert label=="E1RA" and mod=="Raw54E1RATriple123" and sep==":" and list(map(int,ids))==[1,2,3]
            ns="BB6.Agent8Raw54.E1RATriple123"
            for i,k in zip(map(int,ids),("one","two","three")):
                put(misses[i],f".proven ({ns}.table .{k}) ({ns}.never .{k})",mod)
                tags[tag]+=1
        elif tag=="U":
            assert label=="E1OneRC" and v==["139"]
            proved(139,"Raw54E1OneRCHard139","BB6.Agent8Raw54.E1OneRC.M139");tags[tag]+=1
        elif tag in ("H","Z"):
            i=int(v[0]);code=misses[i]
            late(label[-2:].lower(),i,code,[tag,*v[1:]],ROOT,500,label=label)
            mod=f"Raw54{label}Late{i}"
            ns=f"BB6.Agent8Raw54.{label}Late{i}"
            if tag=="Z":
                proved(i,mod,ns)
            else:
                n,s=map(int,v[1:])
                B=n+1+maxdelay(rowdata(code))
                assert B<=spec["bound"],(i,B)
                put(code,f".last {n} {slot(s)}",mod)
                proof=f"BB6.Agent8Raw54.LateBridge.last_mono (B := {B}) (C := {spec['bound']}) (p := {ns}.table) (n := {n}) (s := {slot(s)}) {ns}.checked (by decide)"
                leaf_checks[parse(code)]=(mod,ns+".table",proof)
            tags[tag]+=1
        else:raise ValueError(line)
    assert tags==spec["tags"],tags
    assert set(certs)==set(rows)
    return json.loads((work/"tree.json").read_text()),certs,deps,leaf_checks

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("label",choices=SPECS)
    ap.add_argument("--threshold",type=int,default=80)
    args=ap.parse_args()
    assert args.threshold>0
    label=args.label;spec=SPECS[label];B=spec["bound"]
    ns="BB6.Agent8Raw54."+label
    base="Raw54"+label+"Base"
    w,q={"E1RA":("false",0),"E1RB":("false",1),"E1OneRC":("true",2),"E1OneRE":("true",4)}[label]
    (ROOT/(base+".lean")).write_text(f"""import Raw54Base
namespace {ns}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
abbrev parent : PartialMachine := refine BB6.Agent8Raw54.raw54 (4,true) (some ⟨{w},true,{q}⟩)
theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
  weightedTNFNoAssignedHalt_refine _ _ _ (weightedTNFNoAssignedHalt_refine _ _ _
    (pathEnd_nohalt root 2 (path.take 3) firstOneCylinder_no_assigned_halt))
end {ns}
""")
    with tempfile.TemporaryDirectory() as d:
        tree,certs,deps,leaf_checks=collect(Path(d),label)
        assemble(ROOT,tree,certs,deps,spec["parent"],B,label,ns,base,spec["stats"],args.threshold,leaf_checks)
        root=ROOT/("Raw54"+label+"Complete.lean")
        attainer=f"Raw54{label}Late{spec['attainer']}"
        ans=f"BB6.Agent8Raw54.{label}Late{spec['attainer']}"
        suffix=f"""
namespace {ns}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
theorem exact_threshold (B : Nat) : (∀ m, compatible parent m → WeightedBound B m) ↔ {B} ≤ B := by
  constructor
  · intro h
    obtain ⟨m,hm,hh,hd⟩ := {ans}.attained
    have hb := h m hm {spec['n']} {spec['delay']} hh hd
    omega
  · intro h m hm k d hk hd
    exact Nat.le_trans (complete_cover m hm k d hk hd) h
#print axioms exact_threshold
end {ns}
"""
        root.write_text("import "+attainer+"\n"+root.read_text()+suffix)
if __name__=="__main__":main()
