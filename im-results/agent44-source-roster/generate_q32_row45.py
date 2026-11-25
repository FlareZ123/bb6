#!/usr/bin/env python3
"""Regenerate exact row45 finite prefix; preserve all unresolved leaves."""
from collections import Counter
import json
import generate_q32_slice as core

def main():
    spec=json.loads((core.HERE/"Q32Row45Discovery.json").read_text())
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
    core.emit_one(45,p,tree,residuals)
    print(json.dumps(spec,indent=2),flush=True)

if __name__=="__main__":
    main()
