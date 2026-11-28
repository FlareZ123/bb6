#!/usr/bin/env python3
"""Accelerate one frozen exact partition without modifying shared modules."""
import json
import re
import sys
from pathlib import Path
from collections import defaultdict
from partial_ngram_quotient import transform as compact
from prefix_rewrite import transform as prefix

def dependencies(g, roots):
    seen=set()
    def visit(m):
        if m in seen:
            return
        f=g/(m+".lean")
        if not f.is_file():
            return
        seen.add(m)
        for dep in re.findall(r"^import\s+(\S+)",f.read_text(),re.M):
            visit(dep)
    for root in roots:
        visit(root)
    return seen

def repair(g, branch, part):
    plan=json.loads((g/"split-plan.json").read_text())
    assert plan["artifact_prefix"]=="raw42-split-"+branch
    groups=plan["groups"]
    usage=defaultdict(set)
    for key,roots in groups.items():
        for m in dependencies(g,roots):
            usage[m].add(key)
    nleaf=nroot=nshared=0
    for m in sorted(usage):
        if part not in usage[m]:
            continue
        f=g/(m+".lean")
        src=f.read_text()
        if re.fullmatch(r"Raw42"+branch+r"(NGram|Run)\d+",m) and len(src)>7000:
            assert usage[m]=={part}, (m,usage[m])
            out,b,a=compact(src)
            f.write_text(out)
            print(m,b,"->",a,flush=True)
            nleaf+=1
        elif m.startswith("Raw42"+branch+"ClosedRoot"):
            assert usage[m]=={part}, (m,usage[m])
            out,n,s,k=prefix(src,branch)
            if n:
                f.write_text(out)
                nroot+=n
                nshared+=s
    print("partition",branch,part,"compacted leaves",nleaf,"accelerated checks",nroot,"shared prefix checks",nshared,flush=True)

if __name__=="__main__":
    repair(Path(sys.argv[1]),sys.argv[2],sys.argv[3])
