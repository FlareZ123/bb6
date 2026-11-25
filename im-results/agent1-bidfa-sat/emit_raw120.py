#!/usr/bin/env python3
"""Emit exact raw120 1LB SAT witnesses with the existing source checker."""
from pathlib import Path
import json,sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/"agent16-raw118"))
from tree_emit import emit
data=json.loads((HERE/"raw120-1lb-hits.json").read_text())
print("import TreeBiDFA\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6Coverage.Agent1BiDFASat.Raw120LB\nopen BB6Coverage Agent16BiDFA.TreeCheck")
for hit in data:
    code,n,m=emit(hit["index"],hit["table"],hit["left"],hit["right"])
    assert (n,m)==(hit["states"],hit["edges"])
    print(code)
print("end BB6Coverage.Agent1BiDFASat.Raw120LB")
