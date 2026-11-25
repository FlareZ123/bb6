#!/usr/bin/env python3
"""Replay exact symbolic plans and emit existing SweepPumping proofs."""
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/"agent31-three-hole-tnf"))
import generate_sweeps as sw

def replay(spec):
    p=sw.parse(spec["table"])
    start=sw.C(spec["q"],0,0,sw.W(*spec["left"]),sw.W(*spec["right"]))
    c0=sw.C(0,0,0,sw.W(),sw.W())
    for _ in range(spec["entry"]): c0=sw.step(p,c0)
    assert c0.q==start.q and c0.l.pre==start.l.pre+start.l.suf
    assert c0.r.pre==start.r.pre+start.r.suf
    def grow(w):
        return sw.W(w.pre+w.block,w.block,w.suf)
    target=sw.C(start.q,spec["delta"],0,grow(start.l),grow(start.r))
    c=start
    history=[]
    for cmd in spec["cmds"]:
        if isinstance(cmd,int):
            for _ in range(cmd):
                d=sw.step(p,c)
                history.append(("step",c,d,1))
                c=d
        else:
            side,cut,k,I,O=cmd
            w=c.l if side=="L" else c.r
            other=c.r if side=="L" else c.l
            assert w.block==I and not other.block
            assert sw.local(p,c.q,w.pre if side=="L" else other.pre[:cut],
                            other.pre[:cut] if side=="L" else w.pre,
                            side,I)==(k,O)
            ow=sw.W(other.pre[:cut],O,other.pre[cut:]+other.suf)
            if side=="L":
                d=sw.C(c.q,c.h0,c.hn-len(I),sw.W(w.pre+w.suf),ow)
            else:
                d=sw.C(c.q,c.h0,c.hn+len(I),ow,sw.W(w.pre+w.suf))
            history.append(("loop",c,d,k,side,I,O,cut))
            c=d
    assert c.norm()==target.norm()
    code,info=sw.generate(f"Q32_{spec['i']}",p,
                           (spec["entry"],c0,start,target,(history,c)))
    assert info==(spec["entry"],spec["intercept"],spec["slope"]),info
    return code

def main():
    specs=json.loads((HERE/"q32_sweep_plans.json").read_text())
    assert [s["i"] for s in specs]==list(range(1,14))
    manifest=json.loads((HERE/"Q32SliceManifest.json").read_text())
    residuals={x for r in manifest["audited"] for x in r["residuals"]}
    cubic="1RB1RD_1RC1LB_0LA0RE_1LA0LB_1LF1RE_---1LA"
    assert residuals=={cubic,*[s["table"] for s in specs]}
    code=["import SweepPumping","set_option maxRecDepth 100000",
          "set_option maxHeartbeats 0","set_option linter.unusedVariables false",
          "namespace BB6Coverage.Agent31Pump","open BB6Coverage"]
    code += [replay(s) for s in specs]
    code.append("end BB6Coverage.Agent31Pump")
    (HERE/"Q32SweepData.lean").write_text("\n\n".join(code)+"\n",encoding="utf-8")

if __name__=="__main__":
    main()
