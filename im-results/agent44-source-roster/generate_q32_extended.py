#!/usr/bin/env python3
"""Complete five-hole row audits using FAR plus generated all-length sweeps.

Reuse Agent31's proof emitter and Agent44's exact source audit emitter.
Every symbolic leaf is a .proven constructor with a kernel-checked theorem.
"""
import argparse
from collections import Counter
import json
import generate_q32_slice as core
from generate_q32_sweeps import sw

CONFIG = {
    28: ("1RB1RD_1RC1LC_0LA---_1LA0LB_------_------", 131, 24, [
        (0,0,1,0,2,3,2,0,2),
        (0,0,1,2,3,2,2,0,3),
        (0,0,1,2,3,4,1,4,4,4,4),
        (0,0,1,2,3,4,4,0,1,4,4),
        (1,0,1,2,3,0,1,0,3),
        (1,0,1,2,3,0,1,4,4,4,4),
    ]),
    35: ("1RB1RD_1RC0RE_0LA---_1LA0LB_------_------", 242, 12, [
        (0,0,1,2,3,0,1,2,3),
        (0,0,1,2,3,4,1,4,4,4,4),
        (0,0,1,2,3,4,4,0,1,4,4),
        (1,0,1,0,2,3,3,3,3),
        (1,0,1,2,1,3,1,4,4,4,4),
        (1,0,1,2,3,2,2,2,3),
    ]),
    36: ("1RB1RD_1RC1LE_0LA---_1LA0LB_------_------", 198, 10, [
        (0,0,1,0,2,0,3,0,3),
        (0,0,1,0,2,3,2,4,1,0,5,0,2),
        (0,0,1,0,2,3,3,3,3),
        (0,0,1,2,1,3,3,3,3),
        (0,0,1,2,3,2,2,2,4,0,1),
        (0,0,1,2,3,2,2,2,4,2,1),
        (0,0,1,2,3,2,2,2,4,2,5,2,1),
        (0,0,1,2,3,2,2,4,2,2,1),
        (0,0,1,2,3,4,4,0,1,4,4),
        (1,0,1,0,2,3,3,3,3),
        (1,0,1,0,2,3,4,3,3,0,0),
        (1,0,1,0,2,3,4,4,4,4,4),
        (1,0,1,2,1,0,3,2,4,5,3,0,3),
        (1,0,1,2,3,0,1,4,4,4,4),
        (1,0,1,2,3,2,2,0,4,2,2),
        (1,0,1,2,3,2,2,0,4,2,5,2,3),
        (1,0,1,2,3,2,2,2,4,0,1),
        (1,0,1,2,3,2,2,2,4,2,5,0,1),
        (1,0,1,2,3,2,2,4,5,0,1,2,2),
        (1,0,1,2,3,3,4,3,3,0,5,3,3),
        (1,0,1,2,3,4,4,0,1,4,4),
        (1,0,1,2,3,4,4,3,1,4,4),
    ]),
    37: ("1RB1RD_1RC1RE_0LA---_1LA0LB_------_------", 106, 0, [
        (0,0,1,0,2,3,2,0,2),
        (0,0,1,2,3,2,2,1,2),
        (0,0,1,2,3,2,2,2,4,0,1),
        (0,0,1,2,3,2,2,2,4,2,1),
        (0,0,1,2,3,2,2,4,2,2,1),
        (0,0,1,2,3,4,4,0,1,4,4),
        (1,0,1,0,2,3,3,3,3),
        (1,0,1,2,1,3,3,4,4,4,4),
        (1,0,1,2,3,2,2,2,4,2,3),
    ]),
}

def extended_candidate(p, ev):
    # Agent31's original candidate checks early extrema. The same symbolic
    # pump verifier allows a wider event window without changing proof trust.
    for i,(t,s,c) in enumerate(ev):
        for j in range(i+1,min(i+24,len(ev))):
            _,s2,d=ev[j]
            if s!=s2 or c.q!=d.q:
                continue
            delta=d.h0-c.h0
            if s=="L" and c.l.pre==d.l.pre=="":
                a,b,side=c.r.pre,d.r.pre,"R"
            elif s=="R" and c.r.pre==d.r.pre=="":
                a,b,side=c.l.pre,d.l.pre,"L"
            else:
                continue
            diff=len(b)-len(a)
            if not 1<=diff<=32:
                continue
            for k in range(len(a)+1):
                if b[:k]!=a[:k] or b[k+diff:]!=a[k:]:
                    continue
                block=b[k:k+diff]
                pred=a[:k]+block*2+a[k:]
                if not any(e[1]==s and e[2].q==c.q and
                    e[2].h0==c.h0+2*delta and
                    (e[2].r.pre if side=="R" else e[2].l.pre)==pred
                    for e in ev[j+1:j+24]):
                    continue
                w=sw.W(a[:k],block,a[k:])
                v=sw.W(a[:k]+block,block,a[k:])
                start=sw.C(c.q,0,0,sw.W() if side=="R" else w,w if side=="R" else sw.W())
                target=sw.C(c.q,delta,0,sw.W() if side=="R" else v,v if side=="R" else sw.W())
                res=sw.pump(p,start,target)
                if res:
                    return t,c,start,target,res
    return None

def run(row):
    root,B,n,bank=CONFIG[row]
    rows,_,todo=core.source_roster()
    p=rows[row]
    assert p==core.parse(root) and p in todo[12:]
    core.B=B
    core.DFAS=[(v,d) for v,d in core.DFAS if len(d)<=6]
    core.DFAS += [(b[0],tuple(b[1:])) for b in bank]
    stats=Counter()
    residuals=[]
    t=core.build(p,stats,residuals)
    assert len(residuals)==n,(row,stats)
    mod=f"Q32Row{row}Sweeps"
    parts=["import SweepPumping","set_option maxRecDepth 100000",
           "set_option maxHeartbeats 0","set_option linter.unusedVariables false",
           "namespace BB6Coverage.Agent31Pump","open BB6Coverage"]
    mapping={}
    proofs=[]
    for j,q in enumerate(sorted(residuals)):
        table=core.fmt(q)
        sp=sw.parse(table)
        ev=sw.concrete_events(sp,limit=50000)[:400]
        ans=sw.candidate(sp,ev) or extended_candidate(sp,ev)
        assert ans is not None,table
        code,info=sw.generate(f"Q32_R{row}_{j:02}",sp,ans)
        parts.append(code)
        mapping[q]=f"BB6Coverage.Agent31Pump.MQ32_R{row}_{j:02}"
        proofs.append({"table":table,"entry":info[0],"intercept":info[1],"slope":info[2]})
    if residuals:
        parts.append("end BB6Coverage.Agent31Pump")
        (core.HERE/(mod+".lean")).write_text("\n\n".join(parts)+"\n",encoding="utf-8")
    def discharge(t):
        if t[0]=="open":
            return ("proven",mapping[t[1]])
        if t[0]=="split":
            return (*t[:3],[discharge(k) for k in t[3]])
        return t
    original_audit=core.audit
    original_emit=core.emit
    def audit(t):
        if t[0]=="proven":
            return f".proven {t[1]}.table {t[1]}.never"
        return original_audit(t)
    def emit(name,imports,body):
        if ".proven " in body:
            imports=imports+[mod]
        return original_emit(name,imports,body)
    core.audit=audit
    core.emit=emit
    try:
        assert core.emit_one(row,p,discharge(t),[])==f"Q32Slice{row}"
    finally:
        core.audit=original_audit
        core.emit=original_emit
    manifest={"queue_index":row,"table":root,"bound":B,
              "stats":dict(stats),"symbolic":proofs,"unresolved":[]}
    (core.HERE/f"Q32Row{row}Manifest.json").write_text(json.dumps(manifest,indent=2)+"\n")
    print(json.dumps(manifest),flush=True)

if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("rows",nargs="+",type=int,choices=sorted(CONFIG))
    for row in ap.parse_args().rows:
        run(row)
