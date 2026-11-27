#!/usr/bin/env python3
"""Check SMT model compact DFA by original Agent47 source FAR reconstruction.

The SMT solver remains an untrusted searcher; the Lean Data.fastValid
checker is the trusted theorem condition once the model is integrated.
"""
from __future__ import annotations
import contextlib
import io
import re
import runpy
import sys
import tempfile
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
GEN=ROOT/"im-results/agent47-raw41-cut/generate_two.py"

def transitions(table):
    s=table.replace("_","")
    assert len(s)==36
    return tuple(-1 if s[i]=="-" else int(s[i])*12+6*(s[i+1]=="R")+ord(s[i+2])-65
                 for i in range(0,36,3))

def main():
    with tempfile.TemporaryDirectory() as td:
        with contextlib.chdir(td),contextlib.redirect_stdout(io.StringIO()):
            g=runpy.run_path(str(GEN))
    hits=0
    for line in sys.stdin:
        if not line.startswith("HIT "):
            continue
        fields=line.split()
        _,idx,table,d,rev,*rest=fields
        d=int(d)
        assert rest.pop(0)=="DFA"
        vals=rest[:2*d]
        assert len(vals)==2*d and all(re.fullmatch("[0-9]",v) for v in vals)
        cert=rev+"".join(vals)
        g["far"](cert,transitions(table)) # checks the DFA by exact fixed-point saturation
        print(f"SOURCE_FAR_VALID line={idx} table={table} code={cert}",flush=True)
        hits+=1
    if not hits:
        print("NO_SMT_CANDIDATE",flush=True)

if __name__=="__main__":
    main()
