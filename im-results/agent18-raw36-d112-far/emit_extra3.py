#!/usr/bin/env python3
"""Regenerate the three extra Raw36 D1=1LA structured source certificates."""
import json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/"agent7-raw36-b1le"))
from stack_candidates import generate
rows=[(t,json.loads(v)) for t,v in
      (line.split("\t") for line in (HERE/"generic_extra3.tsv").read_text().splitlines())]
assert len(rows)==3
generate(rows,sys.argv[1],stem="Raw36D112StructExtra3",
         ns="BB6.Agent18Raw36D112StructExtra")
