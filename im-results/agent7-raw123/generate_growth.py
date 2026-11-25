"""Generate exact affine certificates from the saved 368 seeds.
Search is not repeated: only the selected symbolic phase chain is reconstructed.
"""
from pathlib import Path
from functools import lru_cache, partial
import base64, hashlib, json, sys, zlib
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "agent10-tnf-multipump"))
import multi
from multi import C, clean, lit, rep, prefix, rest, step
local = lru_cache(maxsize=200000)(partial(multi.local, limit=150))

def pump(p, start, target, limit=1200):
    c=start; hist=[]; seen=set(); targetnorm=target.norm()
    for _ in range(limit):
        if c.norm()==targetnorm: return hist,c
        if c in seen: return None
        seen.add(c); ok=False
        for sd in ["L","R"]:
            w,o=(c.l,c.r) if sd=="L" else (c.r,c.l)
            lp=prefix(w); wr=rest(w); op=prefix(o)
            if not wr or len(lp)>64: continue
            I=wr[0][0]; assert wr[0][1]
            for j in range(min(32,len(op))+1):
                ans=local(p,c.q,lp if sd=="L" else op[:j],op[:j] if sd=="L" else lp,sd,I)
                if not ans: continue
                k,O=ans; w2=clean(lit(lp)+wr[1:]); o2=clean(lit(op[:j])+rep(O)+lit(op[j:])+rest(o))
                d=C(c.q,w2,o2) if sd=="L" else C(c.q,o2,w2)
                hist.append(("loop",c,d,k,sd,I,O,j)); c=d; ok=True; break
            if ok: break
        if ok: continue
        try: d=step(p,c)
        except ValueError: return None
        hist.append(("step",c,d,1)); c=d
    return None

def advance(w):
    return clean(sum((lit(s)+rep(s) if b else lit(s) for s,b in w),()))

def rows():
    data=zlib.decompress(base64.b64decode((ROOT/"growth.b64").read_bytes()))
    assert hashlib.sha256(data).hexdigest()=="1743f20a770146faaa0c7cbcc70152a532e050ad6d046cc303c81732235c0b34"
    result=json.loads(data)
    assert len(result)==len({r[0] for r in result})==368
    return result

def generate(out=ROOT, selected=None):
    out=Path(out); out.mkdir(parents=True,exist_ok=True)
    registry={}
    data=rows()
    for i in range(0,len(data),16):
        name=f"Raw123Growth{i//16:02}"
        ns=f"BB6.Agent7{name}"
        code=["import SweepPumping","set_option maxRecDepth 100000","set_option maxHeartbeats 0",
              f"namespace {ns}","open BB6Coverage BB6Coverage.Agent31Pump"]
        for j,(flat,t,q,l,r,a,b) in enumerate(data[i:i+16],i):
            registry[flat]=(name,f"{ns}.M{j}")
            if selected is not None and flat not in selected: continue
            p=multi.parse(flat)
            l=tuple(map(tuple,l)); r=tuple(map(tuple,r))
            st=C(q,l,r); tg=C(q,advance(l),advance(r))
            ans=pump(p,st,tg)
            assert ans is not None,(j,flat)
            hist,_=ans
            assert (sum(x[3] for x in hist if x[0]=="step"),sum(x[3] for x in hist if x[0]=="loop"))==(a,b),(j,flat)
            proof,info=multi.generate(j,p,(t,st,tg,ans))
            code.append(proof)
        code.append(f"end {ns}")
        (out/(name+".lean")).write_text("\n\n".join(code)+"\n")
    return registry

if __name__=="__main__":
    generate()
