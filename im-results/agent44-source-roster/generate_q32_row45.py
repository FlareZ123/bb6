#!/usr/bin/env python3
"""Regenerate and discharge the full row45 tree, retaining exact leaf identities."""
from collections import Counter
import json
import generate_q32_slice as core
from generate_q32_sweeps import replay

def main():
    spec=json.loads((core.HERE/"Q32Row45Discovery.json").read_text())
    plans=json.loads((core.HERE/"Q32Row45SweepPlans.json").read_text())
    rows,_,todo=core.source_roster()
    p=rows[spec["queue_index"]]
    assert core.fmt(p)==spec["table"] and p in todo[12:]
    core.B=spec["bound"]
    core.DFAS=[(b[0],tuple(b[1:])) for b in spec["dfa_bank"]]
    stats=Counter()
    residuals=[]
    tree=core.build(p,stats,residuals)
    assert dict(stats)==spec["stats"],stats
    assert [core.fmt(q) for q in residuals]==spec["unresolved"]
    mod="Q32Row45Sweeps"
    parts=["import SweepPumping","set_option maxRecDepth 100000",
           "set_option maxHeartbeats 0","set_option linter.unusedVariables false",
           "namespace BB6Coverage.Agent31Pump","open BB6Coverage"]
    parts += [replay(s) for s in plans]
    parts.append("end BB6Coverage.Agent31Pump")
    (core.HERE/(mod+".lean")).write_text("\n\n".join(parts)+"\n")
    mapping={}
    for s in plans:
        n=f"BB6Coverage.Agent31Pump.MQ32_{s['i']}"
        mapping[core.parse(s["table"])]=f".proven {n}.table {n}.never"
    for i,j in [(3,9),(5,11),(6,12)]:
        n=f"BB6.Agent44Row45.Counter{i}"
        for k,v in [(i,"true"),(j,"false")]:
            mapping[residuals[k]]=f".proven ({n}.table {v}) ({n}.never {v})"
    assert set(mapping)==set(residuals)
    def discharge(t):
        if t[0]=="open":
            return ("proven",mapping[t[1]])
        if t[0]=="split":
            return (*t[:3],[discharge(k) for k in t[3]])
        return t
    original_audit=core.audit
    original_emit=core.emit
    def audit(t):
        return t[1] if t[0]=="proven" else original_audit(t)
    def emit(name,imports,body):
        if ".proven " in body:
            imports=imports+[mod,"Row45Counters"]
        return original_emit(name,imports,body)
    core.audit=audit
    core.emit=emit
    try:
        core.emit_one(45,p,discharge(tree),[])
    finally:
        core.audit=original_audit
        core.emit=original_emit
    print(json.dumps({**spec,"symbolic_leaves":14,"candidate_unresolved":[]},indent=2),flush=True)

if __name__=="__main__":
    main()
