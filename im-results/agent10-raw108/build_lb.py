"""Merge the pinned raw108 0LB candidate census and generate its special leaves.
Every emitted witness must pass the original-source Lean audit.
"""
from pathlib import Path
from itertools import product
import base64, gzip, json, subprocess, sys, re

ROOT=Path(__file__).resolve().parent
NG=ROOT.parent/"agent1-ngram"
BLOCK=ROOT.parent/"agent13-block-far"
MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]

def load():
    spec=json.loads(gzip.decompress(base64.b64decode((ROOT/"0LB-candidates.json.gz.b64").read_text())))
    extra=json.loads((ROOT/"0LB-extra.json").read_text())
    assert not extra["remaining"]
    assert set(spec["remaining"])==set(extra["block"])|set(extra["manual"])|{"1930"}
    assert spec["split_late"]["1930"]==extra["split_1930"]["query"]
    spec["bound"]=extra["candidate_bound"]
    spec["manual"].update(extra["manual"])
    def params(v):
        width,cap,mod,runs,flip=v
        return dict(width=width,cap=cap,mod=mod,runs=runs,flip=bool(flip))
    spec["block"].update({i:params(v) for i,v in extra["block"].items()})
    spec["delayed"]=extra["split_1930"]
    spec["delayed"]["block"]={i:params(v) for i,v in spec["delayed"]["block"].items()}
    return spec

def emit_ngram_group(spec, opens, target):
    asym=ROOT.parent/"agent32-raw59"
    sys.path.insert(0,str(asym))
    from generate_asym import emit, BASE
    exe=target/"ngram_asym"
    subprocess.run(["g++","-std=c++17","-O3",str(asym/"ngram_asym.cpp"),"-o",str(exe)],check=True)
    ids=sorted(map(int,spec["ngram"]))
    inp="".join(f"{i} {opens[i]} {spec['ngram'][str(i)][0]} {spec['ngram'][str(i)][1]}\n" for i in ids)
    out=subprocess.run([str(exe)],input=inp,text=True,capture_output=True,check=True)
    certs=dict(l.split(maxsplit=1) for l in out.stdout.splitlines())
    assert set(map(int,certs))==set(ids),out.stderr
    for i in ids:
        mod=f"Raw108LBNGram{i}"
        ns=f"{BASE}.{mod}"
        data=certs[str(i)]
        assert list(map(int,data.split()[:3]))==spec["ngram"][str(i)],(i,data.split()[:3],spec["ngram"][str(i)])
        emit(ROOT,mod,opens[i],data)
        spec["manual"][str(i)]=[mod,ns,opens[i]]


def emit_block(mod, ns, table, params, active=False):
    width=params["width"]
    suffix="" if width==3 else str(width)
    if width!=3:
        subprocess.run([sys.executable,str(BLOCK/"specialize.py"),str(width)],check=True)
        if width>=5 or active:
            s=(BLOCK/"SparseBlockFAR.lean").read_text()
            k=2**width
            s=re.sub(r"\b48\b",str(6*k),s)
            s=re.sub(r"\b8\b",str(k),s)
            s=s.replace("import BlockFAR",f"import BlockFAR{width}").replace("namespace BB6BlockFAR","namespace BB6BlockFAR"+suffix).replace("end BB6BlockFAR","end BB6BlockFAR"+suffix)
            (BLOCK/f"SparseBlockFAR{width}.lean").write_text(s)
    sys.path.insert(0,str(BLOCK))
    from generate_multi import generate
    flip=params.get("flip",False)
    sparse=width>=5 or active
    data=generate(table,BLOCK,width,params["cap"],params["mod"],params["runs"],flip,mod,minimize_left=True,sparse=sparse)
    if active:
        from emit_active import specialize_active, emit_active
        specialize_active(BLOCK,width)
        emit_active(data,BLOCK,mod)
    bns=f"BB6BlockFAR{suffix}.{mod}"
    s=f"import {mod}Proof\nimport BlockFARBridge{suffix}\n"
    if flip:s+="import FARBi\n"
    s+=f"\nnamespace {ns}\nopen BB6Coverage\n"
    if flip:
        s+=f"""open BB6Coverage.FAR
def table : PartialMachine := reflectPartial (BB6BlockFAR{suffix}.partialTable {bns}.machine)
theorem reflect_table : reflectPartial table = BB6BlockFAR{suffix}.partialTable {bns}.machine := by
  funext x
  rcases x with ⟨q,b⟩
  have h : ∀ q : Fin 6, ∀ b : Bool, reflectPartial table (q,b) = BB6BlockFAR{suffix}.partialTable {bns}.machine (q,b) := by decide
  exact h q b
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply reflectNever m
  apply BB6BlockFAR{suffix}.transfer_never {bns}.machine (reflectTable m)
  · rw [← reflect_table]
    exact reflectCompatible table m hm
  · exact {bns}.never
"""
    else:
        s+=f"""def table : PartialMachine := BB6BlockFAR{suffix}.partialTable {bns}.machine
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6BlockFAR{suffix}.transfer_never {bns}.machine m hm {bns}.never
"""
    (ROOT/(mod+".lean")).write_text(s+f"\n#print axioms never\nend {ns}\n")

def prepare(spec, opens, target, witnesses, manual, slot):
    emit_ngram_group(spec,opens,target)
    for i,params in spec.pop("block").items():
        mod=f"Raw108LBBlock{i}";ns=f"BB6.Agent10{mod}"
        emit_block(mod,ns,opens[int(i)],params)
        spec["manual"][i]=[mod,ns,opens[int(i)]]
    kids=emit_split1930(spec,opens[1930],manual,slot)
    n,s=spec["delayed"]["query"]
    witnesses[1930]=("subtree",f".split {n} {slot(s)} (byMove [\n"+",\n".join(kids)+"])")

def emit_split1930(spec, base_table, manual, slot):
    d=spec["delayed"];n,s=d["query"]
    assert d["ordinary_order"]=="product('01','LR','ABCDEF')"
    base=base_table.replace("_","")
    assert base=="1RB---_1RC0LB_0RD---_1LD1RE_0RF1LB_1RA0LB".replace("_","")
    assert base[3*s:3*s+3]=="---"
    assert set(map(int,d["last"]))|set(map(int,d["block"]))==set(range(24))
    assert not set(d["last"])&set(d["block"])
    kids=[]
    for i,mv in enumerate(MOVES):
        if str(i) in d["last"]:
            t,h=d["last"][str(i)]
            kids.append(f".last {t} {slot(h)}")
        else:
            mod=f"Raw108LBSplit1930Kid{i}";ns=f"BB6.Agent10{mod}"
            compact=base[:3*s]+mv+base[3*s+3:]
            tab="_".join(compact[j:j+6] for j in range(0,36,6))
            emit_block(mod,ns,tab,d["block"][str(i)],active=True)
            manual.append(mod)
            kids.append(f".proven {ns}.table {ns}.never")
    return kids

if __name__=="__main__":
    assert sys.argv[1:]==["--split1930"]
    emit_split1930(load(),"1RB---_1RC0LB_0RD---_1LD1RE_0RF1LB_1RA0LB",[],
                   lambda i:f"({i//2},{str(bool(i%2)).lower()})")
