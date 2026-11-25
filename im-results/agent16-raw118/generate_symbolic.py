"""Regenerate inductive witnesses with the same proof emitter and wider discovery bounds."""
from pathlib import Path
from functools import lru_cache
import inspect,sys
ROOT=Path(__file__).resolve().parent
IM=ROOT.parent
sys.path[:0]=[str(IM/"agent31-three-hole-tnf"),str(IM/"agent47-raw114-cut")]
import generate_sweeps as p
import multi_sweep as m
SINGLE=list(map(int,"21 31 99 162 161 164 167 166 169 170 217 172 218 219 300 301 302 327 332 335 336 337 338 346 367 377 381 432 438 442 763 1379 1659 1761 1774 1842 1874 1887 1904 1949 2038 2083 2085 2122 2359 2360 3186 3309 3344 3345 3446 3473 3525 4191 4226 4238 4257 4267 4322 4356 5163 5178 5331 5369 5411 5435 5436 5552 5650 5762".split()))
MULTI=list(map(int,"27 35 71 72 73 134 163 165 168 171 297 334 341 1180 1287 1307 1334 1337 1667 1777 1823 1833 1876 1890 2438 2444 2487 3122 3748 4261 4404 4458 4464 4587 5607".split()))
def patch(module,fn,replacements):
    s=inspect.getsource(getattr(module,fn))
    for a,b in replacements:
        assert a in s,(fn,a)
        s=s.replace(a,b)
    exec(s,module.__dict__)
patch(p,"candidate",[("ev[:60]","ev[:240]"),("i+12","i+40"),("diff<=16","diff<=40"),("j+12","j+40")])
patch(m,"infer",[("maxlen=16","maxlen=32"),("out.append((Rep(block),)+rest)","out.append((Rep(block),)+rest)\n                if len(out)>=256: break")])
patch(m,"discover",[("limit=5000","limit=15000"),("g[:60]","g[:100]"),("i+9","i+15"),("j+9","j+15"),("diff<=16","diff<=32")])
events=p.concrete_events
p.concrete_events=lambda t,limit=10000:events(t,limit)[:500]
p.local=lru_cache(maxsize=30000)(p.local)
def generate(rows):
    imports=[];claims=[]
    for ids,kind,search,gen in [(SINGLE,"Single",lambda t:p.candidate(t,p.concrete_events(t)),p.generate),(MULTI,"Multi",m.discover,m.generate)]:
        for group in range(0,len(ids),8):
            name=f"Raw118{kind}{group//8:02}";ns=f"BB6Coverage.Agent31Pump.{name}"
            parts=["import SweepPumping","set_option maxRecDepth 100000","set_option maxHeartbeats 0","set_option linter.unusedVariables false",f"namespace {ns}","open BB6Coverage"]
            for i in ids[group:group+8]:
                t=p.parse(rows[i]);ans=search(t);assert ans is not None,(kind,i,rows[i])
                code,info=gen(i,t,ans);parts.append(code);p.local.cache_clear()
                claims.append((i,f"{ns}.M{i}"));print(kind,i,info,flush=True)
            parts.append(f"end {ns}")
            (ROOT/(name+".lean")).write_text("\n\n".join(parts)+"\n")
            imports.append(name)
    return imports,claims
